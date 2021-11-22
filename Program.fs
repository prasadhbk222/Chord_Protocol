#if INTERACTIVE
#r "nuget: Akka.FSharp"
#r "nuget: Akka.Remote"
#endif

open System
open System.Text
open System.Diagnostics
open System.Security.Cryptography
open Akka.FSharp
open Akka.Remote
open Akka.Routing
open Akka.Actor
open System.Threading


// let chordSystem = ActorSystem.Create("ChordSystem")

// let m = 6
// let numberOfNodes = 5;

type Instructions =
    | FindSuccessor of int * IActorRef
    | CreateChordRing
    | ReturnSuccessor of IActorRef * int
    | ReturnPredecessor of IActorRef * int
    | JoinHelper of IActorRef * int
    | JoinChord of IActorRef
    | InitializeScheduler
    | Stabilize
    | GivePredecessor of IActorRef
    | StabilizeRequest
    | Notify of IActorRef * int
    | NotifyReceive of IActorRef
    | PrintInformation
    | FindKeySuccessor of int
    | FindFastKeySuccessor of int * int * int
    | FindSlowtKeySuccessor of int * int * int
    | CreateFingerTable of int
    | FindFingerSuccessor of int * int * int
    | UpdateFinger of int * int
    | FixFingers
    | KeyFinderRequests
    | RequestScheduler
    | SendHop of int
    | ReportSupervisor of int
    | SlowKeyFinderRequests
    | RequestSlowScheduler

let hashFunction (hashInput: string) =
    let hashOutput=
        hashInput
        |> Encoding.UTF8.GetBytes
        |> (new SHA1Managed()).ComputeHash
        |> Array.map (fun (x : byte) -> String.Format("{0:X2}", x))
        |> String.concat ""
    hashOutput

let Supervisor numberOfNodes numberOfRequests (chordSystem : ActorSystem) (mailbox: Actor<_>) =
    let mutable totalhop = 0
    let mutable count = 0
    let rec loop() = actor{
        let! message = mailbox.Receive();
        let sender = mailbox.Sender();

        match message with
        | ReportSupervisor nodeHop ->
            totalhop <- totalhop + nodeHop
            count <- count + 1
            if count = numberOfNodes then
                printfn "total hop %i" totalhop
                printfn "average hop count is %f" (float totalhop / float (numberOfRequests * numberOfNodes))
                Environment.Exit(0)


        return! loop()
    }
    loop()

let Peer n inputnumberOfRequests supervisor (NodePosition : int) (chordSystem : ActorSystem) (mailbox: Actor<_>) =

    let mutable successor : IActorRef = null
    let mutable successorIdentifier = -1
    let mutable predecessor : IActorRef = null
    let mutable predecessorIdentifier = -1
    let mutable m = n

    let mutable fingerTableIdentifiers = Array.create m 0
    let mutable fingerTableReferences = Array.create m null
    let mutable fingerTableSize = n
    let mutable fingerPosition = 0
    let mutable numberOfRequests = inputnumberOfRequests
    let mutable cancellation: IScheduler = null
    let mutable hopSum = 0
    let mutable remainingRequests = inputnumberOfRequests

    //let mutable fingerTable = Array2D.init 6,2

    let identifier = NodePosition

    let rec loop() = actor{
        let! message = mailbox.Receive();
        let sender = mailbox.Sender();

        match message with
        | CreateChordRing ->
            predecessor <- null;
            predecessorIdentifier <- -1;
            successor <- mailbox.Self;
            successorIdentifier <- identifier;
            //printfn "In CreateChordRing"
            //mailbox.Self <! PrintInformation

        | CreateFingerTable size ->
            for x in [0 .. size - 1] do
                let key = (identifier + pown 2 x) % pown 2 m
                //printfn "values in fingertable are %i" key
                //fingerTableSize <- size
                mailbox.Self <! FindFingerSuccessor(identifier, x, key)

        | FindFingerSuccessor (originator, position, key) ->
            // only one node present on chord ring
            if (identifier = successorIdentifier) then
                let actorPath =  @"akka://chordSystem/user/" + string originator
                let originatorRef = select actorPath chordSystem
                originatorRef <! UpdateFinger(position, identifier)


            // if succesor of node is on other side of the ring (beyond 0) and key is on same side as node
            // eg node is 4, node.successor is 1 and key is 6
            elif (identifier > successorIdentifier && key > identifier && key > successorIdentifier) then 
                let actorPath =  @"akka://chordSystem/user/" + string originator
                let originatorRef = select actorPath chordSystem
                originatorRef <! UpdateFinger(position, successorIdentifier)

            // if succesor of node is on other side of the ring (beyond 0) and key is on other side of node
            // eg node is 5, node.successor is 2 and key is 1
            elif (identifier > successorIdentifier && key < identifier && key < successorIdentifier) then
                let actorPath =  @"akka://chordSystem/user/" + string originator
                let originatorRef = select actorPath chordSystem
                originatorRef <! UpdateFinger(position, successorIdentifier)

            // eg node is 2, node,succesor is 5 and target is 4
            elif (key > identifier && key <= successorIdentifier) then
                let actorPath =  @"akka://chordSystem/user/" + string originator
                let originatorRef = select actorPath chordSystem
                originatorRef <! UpdateFinger(position, successorIdentifier)

            else
                successor <! FindFingerSuccessor(originator, position, key)


        | UpdateFinger (position, updatedFinger) ->
            fingerTableIdentifiers.[position] <- updatedFinger
            let actorPath =  @"akka://chordSystem/user/" + string updatedFinger
            let updatedFingerRef = select actorPath chordSystem
            fingerTableReferences.[position] <- updatedFingerRef


        | FixFingers ->

            fingerPosition <- fingerPosition + 1
            // let key = (identifier + pown 2 fingerPosition) % pown 2 m
            if (fingerPosition > m-1) then
                fingerPosition <- 0
            let key = (identifier + pown 2 fingerPosition) % pown 2 m
            mailbox.Self <! FindFingerSuccessor(identifier, fingerPosition, key)
            
        

        | FindKeySuccessor (key) ->
            // only one node present on chord ring
            if (identifier = successorIdentifier) then
                printfn "key : %i , successorNode : %i" key identifier

            // if succesor of node is on other side of the ring (beyond 0) and key is on same side as node
            // eg node is 4, node.successor is 1 and key is 6
            elif (identifier > successorIdentifier && key > identifier && key > successorIdentifier) then 
                printfn "key : %i , successorNode : %i" key successorIdentifier

            // if succesor of node is on other side of the ring (beyond 0) and key is on other side of node
            // eg node is 5, node.successor is 2 and key is 1
            elif (identifier > successorIdentifier && key < identifier && key < successorIdentifier) then
                printfn "key : %i , successorNode : %i" key successorIdentifier

            // eg node is 2, node,succesor is 5 and target is 4
            elif (key > identifier && key <= successorIdentifier) then
                printfn "key : %i , successorNode : %i" key successorIdentifier

            else
                successor <! FindKeySuccessor(key)


        | SendHop hopreceived ->
            if remainingRequests > 0 then
                hopSum <- hopSum + hopreceived
                remainingRequests <- remainingRequests - 1
                
            // hopSum <- hopSum + hopreceived
            // remainingRequests <- remainingRequests - 1
            // if (remainingRequests = 0) then
            //     // printfn "identifier : %i -> hopsum : %i" identifier hopSum
            //     supervisor <! ReportSupervisor hopSum

        | FindSlowtKeySuccessor (key, hop, originIdentifier) ->
            // only one node present on chord ring
            if (identifier = successorIdentifier) then
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop


            // if succesor of node is on other side of the ring (beyond 0) and key is on same side as node
            // eg node is 4, node.successor is 1 and key is 6
            elif (identifier > successorIdentifier && key > identifier && key > successorIdentifier) then 
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop

            // if succesor of node is on other side of the ring (beyond 0) and key is on other side of node
            // eg node is 5, node.successor is 2 and key is 1
            elif (identifier > successorIdentifier && key < identifier && key < successorIdentifier) then
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop

            // eg node is 2, node,succesor is 5 and target is 4
            elif (key > identifier && key <= successorIdentifier) then
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop

            else
                successor <! FindSlowtKeySuccessor(key, hop+1, originIdentifier)


        | FindFastKeySuccessor (key, hop, originIdentifier) ->

            // only one node present on chord ring
            if (identifier = successorIdentifier) then
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop


            // if succesor of node is on other side of the ring (beyond 0) and key is on same side as node
            // eg node is 4, node.successor is 1 and key is 6
            elif (identifier > successorIdentifier && key > identifier && key > successorIdentifier) then 
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop

            // if succesor of node is on other side of the ring (beyond 0) and key is on other side of node
            // eg node is 5, node.successor is 2 and key is 1
            elif (identifier > successorIdentifier && key < identifier && key < successorIdentifier) then
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop

            // eg node is 2, node,succesor is 5 and target is 4
            elif (key > identifier && key <= successorIdentifier) then
                printfn "origin : %i, key : %i , successorNode : %i , hops required : %i" originIdentifier key successorIdentifier hop
                let actorPath =  @"akka://chordSystem/user/" + string originIdentifier
                let origin = select actorPath chordSystem
                origin <! SendHop hop

            else
                let mutable i = m-1
                while i >= 0 do
                    let currentFinger = fingerTableIdentifiers.[i]

                    if (identifier > key && currentFinger > identifier && currentFinger > key) then
                        let actorPath =  @"akka://chordSystem/user/" + string currentFinger
                        let currentFingerRef = select actorPath chordSystem
                        currentFingerRef <! FindFastKeySuccessor (key, hop + 1, originIdentifier)
                        i <- -1

                    elif (identifier > key && currentFinger < identifier && currentFinger < key) then
                        let actorPath =  @"akka://chordSystem/user/" + string currentFinger
                        let currentFingerRef = select actorPath chordSystem
                        currentFingerRef <! FindFastKeySuccessor (key, hop + 1, originIdentifier)
                        i <- -1

                    elif (currentFinger > identifier && currentFinger < key) then
                        let actorPath =  @"akka://chordSystem/user/" + string currentFinger
                        let currentFingerRef = select actorPath chordSystem
                        currentFingerRef <! FindFastKeySuccessor (key, hop + 1, originIdentifier)
                        i <- -1

                    i <- i - 1;


        | FindSuccessor (targetIdentifier,target) ->
            // if only one node is present in the system
            if (identifier = successorIdentifier) then
                printfn "2nd node is %i" targetIdentifier
                target <! ReturnSuccessor(successor, successorIdentifier)
                successor <- target
                successorIdentifier <- targetIdentifier

            // if succesor of node is on other side of the ring (beyond 0) and target is on same side as node
            // eg node is 4, node.successor is 1 and target is 6
            elif (identifier > successorIdentifier && targetIdentifier > identifier && targetIdentifier > successorIdentifier) then 
                target <! ReturnSuccessor(successor, successorIdentifier)

            // if succesor of node is on other side of the ring (beyond 0) and target is on other side of node
            // eg node is 5, node.successor is 2 and target is 1
            elif (identifier > successorIdentifier && targetIdentifier < identifier && targetIdentifier < successorIdentifier) then
                target <! ReturnSuccessor(successor, successorIdentifier)

            // eg node is 2, node,succesor is 5 and target is 4
            elif (targetIdentifier > identifier && targetIdentifier <= successorIdentifier) then
                target <! ReturnSuccessor(successor, successorIdentifier)

            else
                successor <! FindSuccessor(targetIdentifier, target)

        // succesor found and returned by find successor method
        | ReturnSuccessor (foundSuccessor, foundSuccessorIdentifier) ->
            let oldsuccessorIdentifier = successorIdentifier
            successor <- foundSuccessor
            successorIdentifier <- foundSuccessorIdentifier
            // initializing all entries of finger table with successor
            for x in [0..m-1] do
                fingerTableIdentifiers.[x] <- successorIdentifier
                let actorPath =  @"akka://chordSystem/user/" + string successorIdentifier
                let successorRef = select actorPath chordSystem
                fingerTableReferences.[x] <- successorRef
            if oldsuccessorIdentifier = -1 then
                mailbox.Self <! InitializeScheduler

            

            // mailbox.Self <! PrintInformation
            //mailbox.Self <! InitializeScheduler

        // node established in the chord ring helping to join a new node
        | JoinHelper (newNode, newNodeIdentifier) ->
            //printfn "Current identifier %i in message JoinHelper, newNode = %A" identifier newNode
            mailbox.Self <! FindSuccessor(newNodeIdentifier, newNode)

        // node joining chord ring with help of one known node
        | JoinChord knownNode ->
            //printfn "Current identifier %i in message JoinChord, knownNode = %A" identifier knownNode
            knownNode <! JoinHelper (mailbox.Self, identifier)

        // start of stabilize protocol
        // ask for predecessor from successor
        | StabilizeRequest ->
            successor <! GivePredecessor mailbox.Self

        // give own predecessor to node sending stabilize request
        | GivePredecessor stabilizeRequestor ->
            stabilizeRequestor <! ReturnPredecessor (predecessor, predecessorIdentifier)

        // predecessor returned by original successor

        | ReturnPredecessor (node, nodeIdentifier) ->

            // these 3 conditions are cases in which predecessor returned by original successor is between 
            // identifer and successor and therefore succcessor should be updated to the predecessor returned by original successor
            if nodeIdentifier <> -1 then
                if (identifier > successorIdentifier && nodeIdentifier > identifier && nodeIdentifier > successorIdentifier) then 
                    successor <- node
                    successorIdentifier <- nodeIdentifier


                elif (identifier > successorIdentifier && nodeIdentifier < identifier && nodeIdentifier < successorIdentifier) then
                    successor <- node
                    successorIdentifier <- nodeIdentifier


                elif (nodeIdentifier > identifier && nodeIdentifier < successorIdentifier) then
                    successor <- node
                    successorIdentifier <- nodeIdentifier


            successor <! Notify (mailbox.Self, identifier)

        | Notify (probablePredecessor, probPredId) ->
            // if (predecessorIdentifier = -1) then  
            //     predecessor <- probablePredecessor
            //     predecessorIdentifier <- probPredId

            // 3 cases in which probablePredecessor is between original predecessor and node
            if ((predecessorIdentifier = -1)||(identifier < predecessorIdentifier && probPredId > identifier && probPredId > predecessorIdentifier)) then
                predecessor <- probablePredecessor
                predecessorIdentifier <- probPredId
            elif ((predecessorIdentifier = -1)||(identifier < predecessorIdentifier && probPredId < identifier && probPredId < predecessorIdentifier)) then
                predecessor <- probablePredecessor
                predecessorIdentifier <- probPredId
            elif ((predecessorIdentifier = -1)||(identifier > predecessorIdentifier && probPredId < identifier && probPredId > predecessorIdentifier)) then
                predecessor <- probablePredecessor
                predecessorIdentifier <- probPredId

            mailbox.Self <! FixFingers

        | InitializeScheduler ->
           // printfn "Scheduler called for %i" identifier
            chordSystem.Scheduler.ScheduleTellRepeatedly(TimeSpan.FromMilliseconds(200.0),TimeSpan.FromMilliseconds(1000.0), mailbox.Self, StabilizeRequest)
            

        | RequestScheduler ->
            if remainingRequests > 0 then
                mailbox.Self <! KeyFinderRequests
                chordSystem.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(1000.0), mailbox.Self, RequestScheduler)
            else
                supervisor <! ReportSupervisor hopSum
            // while numberOfRequests > 0 do
            //     chordSystem.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(1000.0), mailbox.Self, KeyFinderRequests)
            //     numberOfRequests <- numberOfRequests - 
        | RequestSlowScheduler ->
            if remainingRequests > 0 then
                mailbox.Self <! SlowKeyFinderRequests
                chordSystem.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(1000.0), mailbox.Self, RequestSlowScheduler)
            else
                supervisor <! ReportSupervisor hopSum



        | KeyFinderRequests ->
            let key = Random().Next(1, pown 2 m)
            mailbox.Self <! FindFastKeySuccessor(key, 1, identifier)

        | SlowKeyFinderRequests ->
            let key = Random().Next(1, pown 2 m)
            mailbox.Self <! FindSlowtKeySuccessor(key, 1, identifier)

        

        | PrintInformation ->
            //printfn "in PrintInformation"
            // printfn " predecessor: %i, Identifier : %i, succesor: %i" predecessorIdentifier identifier successorIdentifier
            // printfn "Finger table"
            // for x in [0..fingerTableSize-1] do
            //     printfn "position %i : %i" x fingerTableIdentifiers.[x]
            printfn ""

        


        return! loop()
    }
    loop()



[<EntryPoint>]
let main argv =
    let chordSystem = ActorSystem.Create("chordSystem")
    let m = 20
    let numberOfNodes = (int) argv.[0];
    let numberOfRequests = (int) argv.[1];
    let fastmode = (int) argv.[2]
    let supervisorRef = spawn chordSystem "supervisor" (Supervisor numberOfNodes numberOfRequests chordSystem)
    let mutable firstNode: IActorRef = null
    let mutable  nodeArray = [||]
    nodeArray <- Array.zeroCreate(numberOfNodes)
    let mutable usedPositionsSet = Set.empty
    let mutable x = 1
    while x <= numberOfNodes do
    // for x in [1 .. numberOfNodes] do

        let NodePosition = Random().Next(1, pown 2 m)
        //printf "%A" usedPositionsSet
        if usedPositionsSet.Contains(NodePosition) then
            x <- x-1
        else
            usedPositionsSet <- usedPositionsSet.Add(NodePosition)

            printfn "%i Node position is %i" x NodePosition
            // slet actorName: string= "node" + string(NodePosition)
            let actorName: string= string(NodePosition)
            let PeerRef = spawn chordSystem actorName (Peer m numberOfRequests supervisorRef NodePosition chordSystem)
            nodeArray.[x-1] <- PeerRef
            if x = 1 then
                firstNode <- PeerRef
                PeerRef <! CreateChordRing
            else 
                PeerRef <! JoinChord firstNode
            PeerRef <! InitializeScheduler 
        x <- x + 1


    //for x in [0 .. numberOfNodes - 1] do
        //printfn "initializing scheduler"
        //nodeArray.[x] <! InitializeScheduler

    Thread.Sleep(20000);
    
    // for x in [0 .. numberOfNodes - 1] do
    //     Thread.Sleep(1000);
    //     nodeArray.[x] <! PrintInformation

    // printfn " "


    // for x in [0 .. 9] do
    //     Thread.Sleep(1000);
    //     let key = Random().Next(1, pown 2 6)
    //     nodeArray.[0] <! FindKeySuccessor key

    // for x in [1 .. numberOfNodes] do 
    //     nodeArray.[x-1] <! CreateFingerTable m

    Thread.Sleep(25000);

    printfn "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
    // for x in [0 .. numberOfNodes - 1] do
    //     Thread.Sleep(1000);
    //     printfn "Final information of node %A" nodeArray.[x] 
    //     nodeArray.[x] <! PrintInformation

    printfn "########################################################"
    // for x in [0 .. 9] do
    //     Thread.Sleep(1000);
    //     let key = Random().Next(1, pown 2 6)
    //     nodeArray.[0] <! FindFastKeySuccessor key

    if fastmode = 1 then
        for node in nodeArray do
            Thread.Sleep(100);
            let key = Random().Next(1, pown 2 m)
            node <! RequestScheduler
        
    if fastmode <> 1 then
        for node in nodeArray do
            Thread.Sleep(100);
            let key = Random().Next(1, pown 2 m)
            node <! RequestSlowScheduler


    
    // for x in [0 .. numberOfNodes - 1] do
    //     Thread.Sleep(1000);
    //     nodeArray.[x] <! PrintInformation
 



    System.Console.ReadKey() |> ignore
    printfn "Exiting"

    0