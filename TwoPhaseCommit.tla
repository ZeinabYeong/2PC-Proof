-------------------------- MODULE TwoPhaseCommit --------------------------
EXTENDS Integers, TLAPS
CONSTANTS N

CStates == {"init", "pre-commit", "commit", "abort"}
PStates == {"working", "committed", "aborted", "prepared" }
Participants == 1..N
CoordinatorID == 0


(*
--algorithm TwoPhaseCommit {
   variables cState = "init",
             pState  = [p \in Participants |-> "working"],
             abortFlag = FALSE;
   
  define {
  allPCommit == \A p \in Participants : pState[p] = "prepared" 
  atLeastOneAbort == abortFlag = TRUE
  }


  fair process (Coordinator = CoordinatorID)
    {
c0:     await cState = "init";
        either{
c2:            cState := "abort";}
        or{
           cState := "pre-commit";
c1:        either {
              await allPCommit;
              cState := "commit";}
           or {              
                 await atLeastOneAbort;
                 goto c2;
                 };
             };
    };
               
               
    fair process (Participant \in Participants )
    {
p0:    await pState[self]="working";
       either {
p1:            await cState \in {"pre-commit", "abort"};
               pState[self] := "aborted";
               abortFlag := TRUE;}
         or{     
             await cState = "pre-commit";
             pState[self] := "prepared";
p2:          either {          
                await cState = "commit";
                pState[self] := "committed";}
             or {
               await cState = "abort";
               goto p1;};};}}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "fcd48e67" /\ chksum(tla) = "3e799c9d")
VARIABLES cState, pState, abortFlag, pc

(* define statement *)
allPCommit == \A p \in Participants : pState[p] = "prepared"
atLeastOneAbort == abortFlag = TRUE


vars == << cState, pState, abortFlag, pc >>

ProcSet == {CoordinatorID} \cup (Participants)

Init == (* Global variables *)
        /\ cState = "init"
        /\ pState = [p \in Participants |-> "working"]
        /\ abortFlag = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = CoordinatorID -> "c0"
                                        [] self \in Participants -> "p0"]

c0 == /\ pc[CoordinatorID] = "c0"
      /\ cState = "init"
      /\ \/ /\ pc' = [pc EXCEPT ![CoordinatorID] = "c2"]
            /\ UNCHANGED cState
         \/ /\ cState' = "pre-commit"
            /\ pc' = [pc EXCEPT ![CoordinatorID] = "c1"]
      /\ UNCHANGED << pState, abortFlag >>

c2 == /\ pc[CoordinatorID] = "c2"
      /\ cState' = "abort"
      /\ pc' = [pc EXCEPT ![CoordinatorID] = "Done"]
      /\ UNCHANGED << pState, abortFlag >>

c1 == /\ pc[CoordinatorID] = "c1"
      /\ \/ /\ allPCommit
            /\ cState' = "commit"
            /\ pc' = [pc EXCEPT ![CoordinatorID] = "Done"]
         \/ /\ atLeastOneAbort
            /\ pc' = [pc EXCEPT ![CoordinatorID] = "c2"]
            /\ UNCHANGED cState
      /\ UNCHANGED << pState, abortFlag >>

Coordinator == c0 \/ c2 \/ c1

p0(self) == /\ pc[self] = "p0"
            /\ pState[self]="working"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "p1"]
                  /\ UNCHANGED pState
               \/ /\ cState = "pre-commit"
                  /\ pState' = [pState EXCEPT ![self] = "prepared"]
                  /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << cState, abortFlag >>

p1(self) == /\ pc[self] = "p1"
            /\ cState \in {"pre-commit", "abort"}
            /\ pState' = [pState EXCEPT ![self] = "aborted"]
            /\ abortFlag' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED cState

p2(self) == /\ pc[self] = "p2"
            /\ \/ /\ cState = "commit"
                  /\ pState' = [pState EXCEPT ![self] = "committed"]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
               \/ /\ cState = "abort"
                  /\ pc' = [pc EXCEPT ![self] = "p1"]
                  /\ UNCHANGED pState
            /\ UNCHANGED << cState, abortFlag >>

Participant(self) == p0(self) \/ p1(self) \/ p2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Coordinator
           \/ (\E self \in Participants: Participant(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Coordinator)
        /\ \A self \in Participants : WF_vars(Participant(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Safety ==   \A a, b \in Participants : ~ /\ pState[a] = "aborted"
                                         /\ pState[b] = "committed"

THEOREM setsTheorem ==
    /\ CStates = {"init", "pre-commit", "commit", "abort"}
    /\ PStates = {"working", "committed", "aborted", "prepared" }
    /\ ProcSet = {CoordinatorID} \cup (Participants)
    /\ CoordinatorID \notin Participants
    /\ \A p \in Participants : p # CoordinatorID
    
BY DEF CStates, PStates, ProcSet, CoordinatorID, Participants


TypeOk == /\ cState \in CStates
          /\ pState \in [Participants -> PStates]
          /\ abortFlag \in BOOLEAN
          /\ pc \in [ ProcSet -> { "c0", "c1", "c2", "p0", "p1", "p2", "Done" } ]
          /\ pc[CoordinatorID] \in {"c0", "c1", "c2", "Done"} 
          

cInit == \A p \in Participants:
            /\ cState = "init"
            /\ pState[p] = "working"
            /\ abortFlag = FALSE 
            /\ pc[p] \in {"p0", "p1"}
            
PreCommit == \A p \in Participants:
                /\ cState = "pre-commit"  
                /\ pc[p] \in {"p0", "p1",  "p2", "Done" }
                /\ pc[p] = "Done" => /\ abortFlag = TRUE
                                     /\ pState[p] = "aborted"
                /\ pc[p] = "p2" => pState[p]= "prepared"
                /\ pc[p] \in {"p0", "p1"} => pState[p] = "working"
                
                
Abort == \A p \in Participants:
         /\ cState \in {"init", "pre-commit"}
         /\ pc[p] \in {"p0",  "p1", "p2", "Done" }
         /\ pc[p] = "Done" => /\ abortFlag = TRUE
                              /\ pState[p] = "aborted"
         /\ pc[p] = "p2" => pState[p]= "prepared"
         /\ pc[p] \in {"p0", "p1"} => pState[p] = "working"
         
doneCommit == \A p \in Participants:
                 /\ pc[p] \in {"p2", "Done"} 
                 /\ pState[p]  \in {"prepared", "committed"}
                 /\ pc[p] = "Done" =>  pState[p] = "committed"
                 /\ pc[p] = "p2" => pState[p] = "prepared"
                
              
doneAbort == \A p \in Participants:
                 /\ pc[p] \in {"p0", "p1", "p2", "Done" }
                 /\ pc[p] = "p2" => pState[p] = "prepared"
                 /\ pc[p] = "p1" => pState[p] \in {"working", "prepared"}
                 /\ pc[p] = "p0" => pState[p] = "working"
                 /\ pc[p] = "Done" => /\ pState[p] = "aborted" 
                                      /\ abortFlag = TRUE 
                                      
done == /\ cState \in {"commit", "abort"}
                    
IInv == 
         /\ pc[CoordinatorID] = "c0" =>  cInit                                         
         /\ pc[CoordinatorID] = "c1" => PreCommit    
         /\ pc[CoordinatorID] = "c2" => Abort                                                                                            
         /\ pc[CoordinatorID] = "Done" /\ cState = "commit" =>  doneCommit
         /\ pc[CoordinatorID] = "Done" /\ cState = "abort" =>  doneAbort 
         /\ pc[CoordinatorID] = "Done" /\ cState \in {"pre-commit", "init"} => done 
          
Inv == TypeOk /\ IInv

THEOREM InitImpliesInv ==
ASSUME Init
PROVE Inv
  <1> USE DEF Init
  <1>1. TypeOk
    BY setsTheorem DEF TypeOk
  <1>2. IInv
    BY setsTheorem DEF cInit, IInv
  <1>3. QED
    BY <1>1, <1>2 DEF Inv
    

THEOREM TypeOkInvariant == 
ASSUME TypeOk, Next
PROVE TypeOk'
  <1> USE DEF TypeOk
  <1>1. CASE Coordinator
    BY <1>1, setsTheorem DEF c0, c1, c2, Coordinator
  <1>2. CASE \E self \in Participants: Participant(self)
    BY <1>2, setsTheorem DEF p0, p1,  p2, Participant
  <1>3. CASE Terminating
    BY <1>3, setsTheorem DEF  Terminating, vars
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF Next


THEOREM InvInvariant ==
ASSUME IInv, Next, TypeOk
PROVE Inv'
  <1> USE DEF IInv, TypeOk, Inv
  <1>1. CASE pc[CoordinatorID] = "c0" 
    <2>1. CASE Coordinator 
      <3> USE DEF Coordinator
      <3>1. CASE c0 
        <4>1. (pc[CoordinatorID] = "c0" => cInit)' 
          BY setsTheorem, <2>1, <3>1, <1>1 DEF c0
        <4>2. (pc[CoordinatorID] = "c1" => PreCommit)' 
          BY setsTheorem, <2>1, <3>1, <1>1 DEF c0, PreCommit, cInit 
        <4>3. (pc[CoordinatorID] = "Done" /\ cState = "commit" => doneCommit)'
          BY setsTheorem, <2>1, <3>1, <1>1 DEF c0
        <4>4. (pc[CoordinatorID] = "Done" /\ cState = "abort" =>  doneAbort)'
          BY setsTheorem, <2>1, <3>1, <1>1 DEF  c0
        <4>5. (pc[CoordinatorID] = "c2" => Abort)'
         BY setsTheorem, <2>1, <3>1, <1>1 DEF c0 , cInit, Abort 
        <4>6. (pc[CoordinatorID] = "Done" /\ cState \in {"init","pre-commit"} =>  done)'
         BY setsTheorem, <2>1, <3>1, <1>1 DEF c0
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, TypeOkInvariant
       
      <3>2. CASE c1
       BY setsTheorem, <2>1, <3>2 DEF c1, PreCommit, doneCommit, allPCommit, Abort
      <3>3. CASE c2
       BY setsTheorem, <2>1, <3>3 DEF c2, doneAbort, Abort
      <3>4. QED
       BY <2>1, <3>1, <3>2, <3>3, setsTheorem 
    <2>2. CASE \E self \in Participants: Participant(self)
     
      <3> SUFFICES ASSUME NEW self \in Participants,
                              Participant(self)
                   PROVE Inv'
          BY <2>2
      <3>1. CASE p0(self)
       BY setsTheorem, <2>2, <3>1, <1>1 DEF p0, cInit
      <3>2. CASE p1(self)
        <4>1. (pc[CoordinatorID] = "c0" =>  cInit)'
          BY setsTheorem, <2>2, <3>2 DEF p1,  cInit
        <4>2. (pc[CoordinatorID] = "c1" => PreCommit)'
          BY setsTheorem, <2>2, <3>2 DEF p1, PreCommit
        <4>3. (pc[CoordinatorID] = "c2" => Abort)'
          BY setsTheorem, <2>2, <3>2 DEF p1,  Abort
        <4>4. (pc[CoordinatorID] = "Done" /\ cState = "commit" =>  doneCommit)'
          BY setsTheorem, <2>2, <3>2 DEF p1
        <4>5. (pc[CoordinatorID] = "Done" /\ cState = "abort" =>  doneAbort)'
          BY setsTheorem, <2>2, <3>2 DEF p1, doneAbort 
        <4>6. (pc[CoordinatorID] = "Done" /\ cState \in {"init","pre-commit"} =>  done)'
          BY setsTheorem, <2>2, <3>2 DEF p1, done
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, TypeOkInvariant
        
      <3>3. CASE p2(self)
        <4>1. (pc[CoordinatorID] = "c0" =>  cInit)'
          BY setsTheorem, <2>2, <3>3 DEF p2, cInit
        <4>2. (pc[CoordinatorID] = "c1" => PreCommit)'
          BY setsTheorem, <2>2, <3>3 DEF p2, PreCommit
        <4>3. (pc[CoordinatorID] = "c2" => Abort)'
          BY setsTheorem, <2>2, <3>3 DEF p2, Abort
        <4>4. (pc[CoordinatorID] = "Done" /\ cState = "commit" =>  doneCommit)'
          BY setsTheorem, <2>2, <3>3 DEF p2, doneCommit
        <4>5. (pc[CoordinatorID] = "Done" /\ cState = "abort" =>  doneAbort)'
          BY setsTheorem, <2>2, <3>3 DEF p2, doneAbort
        <4>6. (pc[CoordinatorID] = "Done" /\ cState \in {"init","pre-commit"} =>  done)'
          BY setsTheorem, <2>2, <3>3 DEF p2
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, TypeOkInvariant
        
      <3>4. QED
       BY <2>2, <3>1, <3>2, <3>3, setsTheorem DEF Participant
    <2>3. CASE Terminating
     BY <1>1, <2>3, setsTheorem DEF Terminating
    <2>4. QED
     BY <2>1, <2>2, <2>3 DEF Next
     
  <1>2. CASE pc[CoordinatorID] = "c1" 
    <2>1. CASE Coordinator
      <3> USE DEF Coordinator
      <3>1. CASE c0
       BY setsTheorem, <2>1, <3>1 DEF c0 , PreCommit, cInit, Abort
      <3>2. CASE c1
       BY setsTheorem, <2>1, <3>2 DEF c1, doneCommit, allPCommit , PreCommit, Abort
      <3>3. CASE c2
       BY setsTheorem, <2>1, <3>3 DEF c2, Abort, doneAbort
      <3>4. QED
       BY <2>1, <3>1, <3>2, <3>3, setsTheorem 
    <2>2. CASE \E self \in Participants: Participant(self)
      <3> SUFFICES ASSUME NEW self \in Participants,
                              Participant(self)
                   PROVE Inv'
          BY <2>2
      <3>1. CASE p0(self)
       BY setsTheorem, <2>2, <3>1 DEF p0, cInit, Abort, PreCommit, doneAbort, doneCommit, done
      <3>2. CASE p1(self)
       BY setsTheorem, <2>2, <3>2 DEF p1, doneAbort, PreCommit, cInit, Abort, done
      <3>3. CASE p2(self)
       BY setsTheorem, <2>2, <3>3 DEF p2, doneAbort, doneCommit , PreCommit, cInit, Abort
      <3>4. QED
       BY <2>2, <3>1, <3>2, <3>3, setsTheorem DEF Participant
    <2>3. CASE Terminating
     BY <1>2, <2>3, setsTheorem DEF Terminating
    <2>4. QED
     BY <2>1, <2>2, <2>3 DEF Next 
     
  <1>3. CASE pc[CoordinatorID] = "Done" /\ cState = "commit" 
    <2>1. CASE Coordinator
      <3> USE DEF Coordinator
      <3>1. CASE c0
       BY setsTheorem, <2>1, <3>1 DEF c0, PreCommit, cInit, Abort
      <3>2. CASE c1
       BY setsTheorem, <2>1, <3>2 DEF c1 , doneCommit , allPCommit, PreCommit, Abort
      <3>3. CASE c2
       BY setsTheorem, <2>1, <3>3 DEF c2, doneAbort,  Abort
      <3>4. QED
       BY <2>1, <3>1, <3>2, <3>3, setsTheorem 
    <2>2. CASE \E self \in Participants: Participant(self)
      <3> SUFFICES ASSUME NEW self \in Participants,
                              Participant(self)
                   PROVE Inv'
          BY <2>2
      <3>1. CASE p0(self)
       BY setsTheorem, <2>2, <3>1 DEF p0, PreCommit, cInit, Abort, doneAbort, doneCommit, done
      <3>2. CASE p1(self)
       BY setsTheorem, <2>2, <3>2 DEF p1, doneAbort, PreCommit, cInit, Abort, done
      <3>3. CASE p2(self)
       BY setsTheorem, <2>2, <3>3 DEF p2, doneAbort, doneCommit , PreCommit, cInit, Abort
      <3>4. QED
       BY <2>2, <3>1, <3>2, <3>3, setsTheorem DEF Participant
    <2>3. CASE Terminating
     BY <1>3, <2>3, setsTheorem DEF Terminating, vars, doneCommit
    <2>4. QED
     BY <2>1, <2>2, <2>3 DEF Next 
  <1>4. CASE pc[CoordinatorID] = "Done" /\ cState = "abort"
     <2>1. CASE Coordinator
      <3> USE DEF Coordinator
      <3>1. CASE c0
       BY setsTheorem, <2>1, <3>1 DEF c0, PreCommit, cInit, Abort
      <3>2. CASE c1
       BY setsTheorem, <2>1, <3>2 DEF c1 , doneCommit , allPCommit, PreCommit, Abort
      <3>3. CASE c2
       BY setsTheorem, <2>1, <3>3 DEF c2, doneAbort,  Abort
      <3>4. QED
       BY <2>1, <3>1, <3>2, <3>3, setsTheorem 
    <2>2. CASE \E self \in Participants: Participant(self)
      <3> SUFFICES ASSUME NEW self \in Participants,
                              Participant(self)
                   PROVE Inv'
          BY <2>2
      <3>1. CASE p0(self)
       BY setsTheorem, <2>2, <3>1 DEF p0, PreCommit, cInit, Abort, doneAbort, doneCommit, done
      <3>2. CASE p1(self)
       BY setsTheorem, <2>2, <3>2 DEF p1, doneAbort, PreCommit, cInit, Abort, done
      <3>3. CASE p2(self)
       BY setsTheorem, <2>2, <3>3 DEF  p2, doneAbort, doneCommit , PreCommit, cInit, Abort
      <3>4. QED
       BY <2>2, <3>1, <3>2, <3>3, setsTheorem DEF Participant
    <2>3. CASE Terminating
     BY <1>4, <2>3, setsTheorem DEF Terminating, vars, doneAbort
    <2>4. QED
     BY <2>1, <2>2, <2>3 DEF Next 
  <1>5. CASE pc[CoordinatorID] = "c2" => Abort  
   <2>1. CASE Coordinator
      <3> USE DEF Coordinator
      <3>1. CASE c0
       BY setsTheorem, <2>1, <3>1 DEF c0, PreCommit, cInit, Abort
      <3>2. CASE c1
       BY setsTheorem, <2>1, <3>2 DEF c1 , doneCommit , allPCommit, PreCommit, Abort
      <3>3. CASE c2
       BY setsTheorem, <2>1, <3>3 DEF c2, doneAbort,  Abort
      <3>4. QED
       BY <2>1, <3>1, <3>2, <3>3, setsTheorem 
    <2>2. CASE \E self \in Participants: Participant(self)
      <3> SUFFICES ASSUME NEW self \in Participants,
                              Participant(self)
                   PROVE Inv'
          BY <2>2
      <3>1. CASE p0(self)
       BY setsTheorem, <2>2, <3>1 DEF p0, PreCommit, cInit, Abort, doneAbort, doneCommit, done
      <3>2. CASE p1(self)
       BY setsTheorem, <2>2, <3>2 DEF p1, doneAbort, PreCommit, cInit, Abort, done
      <3>3. CASE p2(self)
       BY setsTheorem, <2>2, <3>3 DEF p2, doneAbort, doneCommit , PreCommit, cInit, Abort
      <3>4. QED
       BY <2>2, <3>1, <3>2, <3>3, setsTheorem DEF Participant
    <2>3. CASE Terminating
     BY <1>4, <2>3, setsTheorem DEF Terminating, vars, doneCommit, done
    <2>4. QED
     BY <2>1, <2>2, <2>3 DEF Next 
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, setsTheorem DEF  Coordinator, Participant
    
THEOREM Invariant ==
ASSUME Inv, Next
PROVE Inv'
BY  TypeOkInvariant,  InvInvariant DEF Inv, TypeOk, IInv, Next  


THEOREM InvImpliesSafety ==
    ASSUME Inv
    PROVE Safety
 <1> USE DEF  IInv, Inv
 <1>1. CASE pc[CoordinatorID] = "c0"
  BY <1>1, setsTheorem DEF cInit, Safety
 <1>2. CASE pc[CoordinatorID] = "c1"
  BY <1>2, setsTheorem DEF PreCommit, Safety 
 <1>3. CASE pc[CoordinatorID] = "c2" 
  BY <1>3, setsTheorem DEF Abort, Safety
 <1>4. CASE pc[CoordinatorID] = "Done" /\ cState = "commit"
  BY <1>4, setsTheorem DEF doneCommit, allPCommit, Safety                                     
 <1>5. CASE pc[CoordinatorID] = "Done" /\ cState = "abort" 
  BY <1>5, setsTheorem DEF doneAbort, atLeastOneAbort, Safety
 <1>6. CASE pc[CoordinatorID] = "Done" /\ cState \in {"pre-commit", "init"}
  BY <1>6, setsTheorem DEF done, Safety
 <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, setsTheorem DEF TypeOk
                   
THEOREM InductiveInvariant == Spec => [] Safety    
<1>1. Init => Inv
  BY InitImpliesInv DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    BY <2>1, Invariant DEF Inv
  <2>2. CASE UNCHANGED vars
    BY <2>2, Invariant DEF Inv, vars, TypeOk, IInv, Abort, doneAbort, doneCommit , PreCommit, cInit, done
  <2>3. QED BY <2>1, <2>2
<1>3. Inv => Safety
  BY SMT, InvImpliesSafety DEFS Safety, Inv 
<1>4. QED BY <1>1,<1>2,<1>3,PTL DEF Spec  


=============================================================================
