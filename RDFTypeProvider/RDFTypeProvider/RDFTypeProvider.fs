namespace Samples.RdfTypeProvider

open System
open System.Reflection
open System.Collections.Generic
open System.IO
open Samples.FSharp.ProvidedTypes
open Microsoft.FSharp.Core.CompilerServices
open Microsoft.FSharp.Quotations
open System.Text.RegularExpressions
    
// type provider implementation


[<TypeProvider>]
type RDFTypeProvider(config: TypeProviderConfig) as this =


    inherit TypeProviderForNamespaces()
    let ns = "Samples.RdfTypeProvider"
    let asm = Assembly.GetExecutingAssembly()


    let createTypes(schemaUrl, numOfIndividuals, schemaSampleAmount, rootTypeName) = 

        let connector = new Connector(schemaUrl)
        
        let serviceType = ProvidedTypeDefinition("RdfService",baseType=Some typeof<Connector>,HideObjectMethods=true)        
       
        let getRdfTypes =
            // FIRST : get explicit types
            let rdfTypesExplicit = connector.getExplicitTypes()
            // SECOND: now we extend types from domains
            let explicitRDFProperties = connector.getExplicitProperties()
            let explicitRDFObjectProperties = connector.getExplicitObjectProperties()
            let rdfTypesOfDomain =  List.concat [ for property in explicitRDFProperties ->  connector.getDomainTypes(property) ]
            // Combine types:  Explicit, Domain (and also Range types)
            rdfTypesExplicit  @ rdfTypesOfDomain |> Seq.distinctBy id
        
        // dictionaries ensure that types are not created multiple times when the RDF graph is explored
        let dictClassTypes = Dictionary<string, ProvidedTypeDefinition>(HashIdentity.Structural)
       // let dictObjectPropTypes = Dictionary<(string * string), ProvidedTypeDefinition>(HashIdentity.Structural)
        let dictCollectionTypes = Dictionary<ProvidedTypeDefinition, ProvidedTypeDefinition * ProvidedTypeDefinition>(HashIdentity.Reference)        // collection type * individual type
        let propContainerTypes = Dictionary<string,ProvidedTypeDefinition>(HashIdentity.Structural)        // collection type * individual type
       // let dictProperties = Dictionary<string, ProvidedProperty>(HashIdentity.Structural)

        
        // containerTypeNameForDomainTypes  is simplified
        

        let rec makePropertiesForRDFType (rdfTypeInGraph: string) (graphType:ProvidedTypeDefinition) isIndividual ultimateRootType =
            (if isIndividual then connector.getPropertiesOfRDFIndividual rdfTypeInGraph 
             else connector.getPropertiesOfRDFClassWithIndividualSamples(rdfTypeInGraph, schemaSampleAmount)) // here we used sampling
            |> List.filter (fst >> String.IsNullOrEmpty >> not)
            |> Seq.groupBy fst  // group by property name
            |> Seq.map(fun (propName,values) ->                 
                let typeName = rdfTypeInGraph + propName + "Container"                
                match propContainerTypes.TryGetValue typeName with
                | (true,propContainerType) -> ProvidedProperty(propName,propContainerType,GetterCode = fun args -> <@@ (%%args.[0]:RdfClass) @@>) 
                | _ ->
                    // if this property group is the special "ns#type" the create the alternative provided type for it
                    if propName = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" then
                        let altClassTypeName = rdfTypeInGraph + propName + "AlterativeTypes"

                        let altClassType = ProvidedTypeDefinition(altClassTypeName, Some typeof<RdfClass>, HideObjectMethods=true) 
                        altClassType.AddMember(ProvidedConstructor([ProvidedParameter("data",typeof<RdfClass>)],InvokeCode = fun args -> <@@ (%%args.[0]:RdfClass) @@> ))

                        values
                        |> Seq.iter( snd >> Option.iter( fun className -> 
                            // class name will be for example "Actor" OR "Person".  The return type this property will be the provided type for that class,
                            // and the instance that this property returns is simply the same data that it already has.  
                            let (altType,_) = findOrCreateType className ultimateRootType false ultimateRootType  
                            altClassType.AddMember(ProvidedProperty(className,altType,GetterCode = fun args -> <@@ (%%args.[0]:RdfClass) @@>))))

                        graphType.AddMember(altClassType) 
                        ProvidedProperty("Alternative", altClassType, GetterCode = fun args -> <@@ (%%args.[0]:RdfClass) @@>)
                    else
                        // create a new provided type  if it doesn't already exist
                        let propContainerType = ProvidedTypeDefinition(typeName, Some typeof<RdfClass>, HideObjectMethods=true)
                        propContainerType.AddMember(ProvidedConstructor([ProvidedParameter("data",typeof<RdfClass>)],InvokeCode = fun args -> <@@ (%%args.[0]:RdfClass) @@> ))
                        values
                        |> Seq.iter( fun (key,value) -> 
                            match value with
                            | None -> // this is a literal 
                                      propContainerType.AddMemberDelayed(fun _ -> ProvidedProperty("Literal",typeof<string list>,GetterCode = fun args -> <@@ (%%args.[0]:RdfClass).GetValue((key,"")) @@> ))
                                    // the value is an URI (class or resource name)
                            | Some(classOrResourceName) ->                            
                                let (providedPropertyType,alreadyExists) = findOrCreateType classOrResourceName graphType false ultimateRootType // check whether this class (represented by this URI) does already exist)
                                let listType = typedefof<list<_>>.MakeGenericType([|providedPropertyType :> Type|])
                                if isIndividual then                                     
                                    propContainerType.AddMemberDelayed(fun _ -> ProvidedProperty(classOrResourceName,listType ,GetterCode = fun args -> <@@ (%%args.[0]:RdfClass).GetValue((key,classOrResourceName)) @@>))
                                else
                                    propContainerType.AddMemberDelayed(fun _ -> ProvidedProperty(classOrResourceName,providedPropertyType, GetterCode = fun args -> <@@ (%%args.[0]:RdfClass).GetValue((key,classOrResourceName))  @@>))
                                if alreadyExists = false then graphType.AddMember providedPropertyType)
                                        
                        graphType.AddMember propContainerType
                        propContainerTypes.Add(typeName,propContainerType)
                        ProvidedProperty(propName,propContainerType,GetterCode = fun args -> <@@ (%%args.[0]:RdfClass) @@>))
            |> Seq.toList


       

        and findOrCreateType name containerType isIndividual ultimateRootType  =
            match dictClassTypes.TryGetValue name with 
            | false,_ -> 
                let t = 
                    if isIndividual then ProvidedTypeDefinition(name, baseType=Some(containerType:>_) ,HideObjectMethods=true)
                    else ProvidedTypeDefinition(name, baseType=Some typeof<RdfClass>,HideObjectMethods=true)
                t.AddMemberDelayed( fun () -> ProvidedConstructor([],InvokeCode = fun _ -> <@@ RdfClass() @@>   ))
                t.AddMembersDelayed (fun () -> makePropertiesForRDFType name containerType isIndividual ultimateRootType)
                
                match isIndividual with
                | false ->      // name refers to an RDF class (not an individual)         
                    // create collection and individuals type for this class
                    let individuals = ProvidedTypeDefinition(name + "Individuals",  Some typeof<obj>, HideObjectMethods=true)
                    let collection = ProvidedTypeDefinition(name ,  Some typeof<obj>, HideObjectMethods=true)
                
                    
                    individuals.AddMembersDelayed(fun () -> 
                        // todo: use the runtime connector, it must be extracted from the underlying service type (which erases to connector) ? somehow ?
                        // or... maybe just make individuals erase down to connector and create a new instance of it ?
                        // just creating a new one at the moment/....
                                [ for ind in connector.getIndividuals(name,numOfIndividuals) |> Seq.distinctBy id  do   
                                    let (individualType,_) = findOrCreateType ind t true ultimateRootType
                                    let p = ProvidedProperty(ind, individualType, 
                                                            GetterCode = (fun args -> 
                                                            <@@
                                                                let connector = new Connector(schemaUrl)                                                            
                                                                RdfClass.Create(connector,ind)            // created for individuals
                                                             @@>))
                                    yield p
                                ])

                    collection.AddMember(ProvidedProperty("Individuals", individuals, GetterCode = fun _ -> <@@ obj() @@>) ) 

                    t.AddMembers [individuals;collection]

                    serviceType.AddMember( ProvidedProperty(name, collection, GetterCode = fun _ -> <@@ obj() @@> )) 
                    dictCollectionTypes.Add(t,(collection,individuals))
                | _ -> containerType.AddMember t
                
                dictClassTypes.Add(name, t)
                
                (t,false)
            | _,t -> 
                (t,true)

  


        let insertRDFTypesForOneGraph (graph : ProvidedTypeDefinition, graphId) = 
            // get all explicit types of graph 
            let allTypesForGraph = getRdfTypes  // graphId is not needed -- as only one graph
            //let theNestedTypesForTheDataTypesClassForDomain = ResizeArray<_>()
            
            [| for rdfTypeInGraph in allTypesForGraph do
                let (itemType,_) = findOrCreateType rdfTypeInGraph graph false graph
                graph.AddMember itemType |]
                
            //theNestedTypesForTheDataTypesClassForDomain |> Seq.toArray




        do serviceType.AddMembers(            
                let makeTypesForGraph(graphName:string) = 
                    let graph = ProvidedTypeDefinition(graphName, Some typeof<obj>,HideObjectMethods=false)
                    graph.AddMembers(insertRDFTypesForOneGraph (graph,graphName) |> Array.toList) 
                    graph
                [ for graph in connector.getGraphs() do 
                    yield makeTypesForGraph (graph) ] )
              
          
        let rootType = ProvidedTypeDefinition(asm, ns, rootTypeName, baseType=Some typeof<Connector>, HideObjectMethods=true)
        rootType.AddMember serviceType
        rootType.AddMembers( 
            [ let meth =
                ProvidedMethod("GetDataContext", [], 
                               serviceType, IsStaticMethod = true,
                               InvokeCode = (fun _ -> <@@ Connector(schemaUrl) @@>))            // generates a connector with SPARQL endpoint located at schemaUrl
              meth.AddXmlDoc "<summary>Returns an instance of the RDF provider using the static paramters</summary>"
              yield meth ] )

        rootType



        
    // basic parameters 
    let paramRdfType = ProvidedTypeDefinition(asm, ns, "RdfDataProvider", Some(typeof<obj>), HideObjectMethods = true)
    let schemaUrl = ProvidedStaticParameter("SchemaUrl",typeof<string>)    
    let individualsAmount = ProvidedStaticParameter("IndividualsAmount",typeof<int>,1000)
    let schemaSampleAmount = ProvidedStaticParameter("SchemaSampleAmount",typeof<int>,100)
    let helpText = "<summary>Some description of the RDF type provider</summary>                    
                   <param name='SchemaUrl'>Some description</param>                    
                   <param name='IndividualsAmount'>Some description</param>"                 
 
    do paramRdfType.DefineStaticParameters([schemaUrl;individualsAmount;schemaSampleAmount], fun typeName args -> 
        createTypes(args.[0] :?> string, // url
                    args.[1] :?> int,    // individuals amount
                    args.[2] :?> int,    // schema sample amount
                    typeName ))


    do paramRdfType.AddXmlDoc helpText                    
    do this.AddNamespace(ns, [paramRdfType])
    
[<TypeProviderAssembly>]
do ()




