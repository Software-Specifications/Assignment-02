---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bin
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,
  authorized = FALSE,

  \* Variable for user
  userTrash = 0,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [command |-> "finished", open |-> FALSE],
  \* Sensor from bin
  binSensor = [sensor |-> "idle"],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = << >>,
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Command for the truck
  truckCommand = [command |-> "emptied", bin |-> 1];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.

\* The outer door can only be locked if it is closed.
OuterDoorLocked == [](outerDoorLocked => ~outerDoorOpen)
\* The vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == [](ramExtended => (outerDoorLocked /\ ~outerDoorOpen))
\* Every time the trash bin is full, it is eventually not full anymore.
TrashEmptied == ~TrashFitsCapacity(MaxUserTrash) ~> TrashFitsCapacity(MaxUserTrash)
\* An unauthorized user cannot open the outer door.
AuthorizedOpenOnly == [](outerDoorOpen => authorized)
\* The user infinitely often has trash and infinitely often has no trash.
UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)
\* Every time the user has trash, they can deposit their trash.
UserTrashDeposited == (userTrash > 0) ~> (userTrash = 0)
\* Every time the truck is requested for the trash bin, the truck has eventually emptied the bin.
TruckEmpties == (truckCommand.command = "request") ~> (truckCommand.command = "emptied")

end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro  

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        \* Open/Close trap door
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          \* Trash falls through
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        \* Extend/Retract ram
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
fair process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* DUMMY truck process type.
\* Remodel it to react to requests and empty the trash bin!
fair process truckProcess \in Trucks
begin
  TruckStart:
    \* Implement behaviour
  while TRUE do
    \* React to a request from the main controller
    TruckAwaitRequest:
      await truckCommand.command = "request";
    \* Drive to the trash bin
    TruckDrive:
      truckCommand := [truckCommand EXCEPT !.command = "arrived"];
    \* empty trash bin by sending "empty"
    TruckEmpty:
      binCommand := [command |-> "empty", open |-> FALSE];
    TruckEmptyDone:
      await binCommand.command = "finished";
    \* the truck informs the main control process that the bin is emptied
    TruckReport:
      truckCommand := [command |-> "emptied", bin |-> truckCommand.bin];
    \* awaits for new requests
  end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* DUMMY main control process type.
\* Remodel it to control the trash bin system and handle requests by users!
fair process controlProcess = Control
variables 
  scan = [user |-> 0, bin |-> 1],
  resp = [user |-> 0, permission |-> FALSE],
  grant = FALSE
begin
  ControlStart:
    \* Implement behaviour
    \* To receive scans from the user
  while TRUE do
    ControllerAwaitScan:
      read(scans, scan);
    ControlAskServer:
      write(serverRequests, [user |-> scan.user]);
    ControlAwaitServer:
      read(serverResponses, resp);
    \* Check the capacity of the bin
    ControlDecide:
      grant := resp.permission /\ TrashFitsCapacity(MaxUserTrash) /\  truckCommand.command = "emptied";
      if grant then
        ControlUnlock:
          binCommand := [command |-> "change_outer_lock", open |-> TRUE];
        ControlUnlockDone:
          await binCommand.command = "finished";
        \* Permission is either answered or declined
        ControlGrant:
          write(permissions, [user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]);
          authorized := TRUE;
        \* If the request is granted, check if the outer door is closed
        ControlAwaitClose:
          await binSensor.sensor = "outer_door_closed";
          binSensor := [sensor |-> "idle"];
        ControlAwaitCloseDone:
          await binCommand.command = "finished";
        ControlLock:
          binCommand := [command |-> "change_outer_lock", open |-> FALSE];
        ControlLockDone:
          await binCommand.command = "finished";
          authorized := FALSE;
        \* Move the deposited trash into the main compartment of the trash bin 
        ControlOpen:
          binCommand := [command |-> "change_trap_door", open |-> TRUE];
        \* The ram should only be extended if the trap door is open
        ControlOpenDone:
          await binCommand.command = "finished";
        \* operate the ram
        ControlExtendRam:
          binCommand := [command |-> "change_ram", open |-> TRUE];
        ControlExtendRamDone:
          await binCommand.command = "finished";
        ControlRetractRam:
          binCommand := [command |-> "change_ram", open |-> FALSE];
        ControlRetractRamDone:
          await binCommand.command = "finished";
        ControlClose:
          binCommand := [command |-> "change_trap_door", open |-> FALSE];
        ControlCloseDone:
          await binCommand.command = "finished";
      else
        ControlDecline:
          write(permissions, [user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]);
      end if;
    ControlTruck:
      if ~TrashFitsCapacity(MaxUserTrash) /\ truckCommand.command = "emptied" then 
        truckCommand := [command  |-> "request", bin |-> 1];
      end if;
  end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d557336c" /\ chksum(tla) = "8f7e4761")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, authorized, userTrash, binCommand, binSensor, scans, 
          permissions, serverRequests, serverResponses, truckCommand, pc

(* define statement *)
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity






TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins


MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded








OuterDoorLocked == [](outerDoorLocked => ~outerDoorOpen)

RamOuterDoor == [](ramExtended => (outerDoorLocked /\ ~outerDoorOpen))

TrashEmptied == ~TrashFitsCapacity(MaxUserTrash) ~> TrashFitsCapacity(MaxUserTrash)

AuthorizedOpenOnly == [](outerDoorOpen => authorized)

UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)

UserTrashDeposited == (userTrash > 0) ~> (userTrash = 0)

TruckEmpties == (truckCommand.command = "request") ~> (truckCommand.command = "emptied")

VARIABLES perm, req, scan, resp, grant

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, authorized, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, pc, 
           perm, req, scan, resp, grant >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ authorized = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 1]
        /\ resp = [user |-> 0, permission |-> FALSE]
        /\ grant = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 163, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 170, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 173, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 185, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 197, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 198, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 199, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 200, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 201, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 205, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, authorized, 
                                           userTrash, binCommand, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, resp, grant >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, authorized, 
                                            userTrash, binSensor, scans, 
                                            permissions, serverRequests, 
                                            serverResponses, truckCommand, 
                                            perm, req, scan, resp, grant >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, authorized, 
                                           userTrash, binCommand, binSensor, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, resp, grant >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, authorized, 
                                      userTrash, binCommand, binSensor, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, req, 
                                      scan, resp, grant >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 232, column 7.")
                               /\ Assert(perm'[self].bin = 1, 
                                         "Failure of assertion at line 233, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               authorized, userTrash, 
                                               binCommand, binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, req, scan, resp, 
                                               grant >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, authorized, 
                                      userTrash, binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, scan, resp, 
                                      grant >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, authorized, 
                                           userTrash, binCommand, binSensor, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, resp, grant >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 240, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          authorized, binCommand, binSensor, 
                                          scans, permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          req, scan, resp, grant >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       authorized, userTrash, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       req, scan, resp, grant >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, authorized, 
                                             userTrash, binCommand, binSensor, 
                                             scans, permissions, 
                                             serverRequests, serverResponses, 
                                             truckCommand, perm, req, scan, 
                                             resp, grant >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, authorized, 
                                      binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, req, 
                                      scan, resp, grant >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       authorized, userTrash, binCommand, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, req, scan, resp, 
                                       grant >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, authorized, 
                                      userTrash, binCommand, binSensor, scans, 
                                      permissions, truckCommand, perm, scan, 
                                      resp, grant >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ pc' = [pc EXCEPT ![self] = "TruckAwaitRequest"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, authorized, 
                                    userTrash, binCommand, binSensor, scans, 
                                    permissions, serverRequests, 
                                    serverResponses, truckCommand, perm, req, 
                                    scan, resp, grant >>

TruckAwaitRequest(self) == /\ pc[self] = "TruckAwaitRequest"
                           /\ truckCommand.command = "request"
                           /\ pc' = [pc EXCEPT ![self] = "TruckDrive"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, authorized, 
                                           userTrash, binCommand, binSensor, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, resp, grant >>

TruckDrive(self) == /\ pc[self] = "TruckDrive"
                    /\ truckCommand' = [truckCommand EXCEPT !.command = "arrived"]
                    /\ pc' = [pc EXCEPT ![self] = "TruckEmpty"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, authorized, 
                                    userTrash, binCommand, binSensor, scans, 
                                    permissions, serverRequests, 
                                    serverResponses, perm, req, scan, resp, 
                                    grant >>

TruckEmpty(self) == /\ pc[self] = "TruckEmpty"
                    /\ binCommand' = [command |-> "empty", open |-> FALSE]
                    /\ pc' = [pc EXCEPT ![self] = "TruckEmptyDone"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, authorized, 
                                    userTrash, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scan, resp, grant >>

TruckEmptyDone(self) == /\ pc[self] = "TruckEmptyDone"
                        /\ binCommand.command = "finished"
                        /\ pc' = [pc EXCEPT ![self] = "TruckReport"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        authorized, userTrash, binCommand, 
                                        binSensor, scans, permissions, 
                                        serverRequests, serverResponses, 
                                        truckCommand, perm, req, scan, resp, 
                                        grant >>

TruckReport(self) == /\ pc[self] = "TruckReport"
                     /\ truckCommand' = [command |-> "emptied", bin |-> truckCommand.bin]
                     /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, authorized, 
                                     userTrash, binCommand, binSensor, scans, 
                                     permissions, serverRequests, 
                                     serverResponses, perm, req, scan, resp, 
                                     grant >>

truckProcess(self) == TruckStart(self) \/ TruckAwaitRequest(self)
                         \/ TruckDrive(self) \/ TruckEmpty(self)
                         \/ TruckEmptyDone(self) \/ TruckReport(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ pc' = [pc EXCEPT ![Control] = "ControllerAwaitScan"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, authorized, userTrash, 
                                binCommand, binSensor, scans, permissions, 
                                serverRequests, serverResponses, truckCommand, 
                                perm, req, scan, resp, grant >>

ControllerAwaitScan == /\ pc[Control] = "ControllerAwaitScan"
                       /\ scans /= <<>>
                       /\ scan' = Head(scans)
                       /\ scans' = Tail(scans)
                       /\ pc' = [pc EXCEPT ![Control] = "ControlAskServer"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, 
                                       authorized, userTrash, binCommand, 
                                       binSensor, permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       req, resp, grant >>

ControlAskServer == /\ pc[Control] = "ControlAskServer"
                    /\ serverRequests' = Append(serverRequests, ([user |-> scan.user]))
                    /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitServer"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, authorized, 
                                    userTrash, binCommand, binSensor, scans, 
                                    permissions, serverResponses, truckCommand, 
                                    perm, req, scan, resp, grant >>

ControlAwaitServer == /\ pc[Control] = "ControlAwaitServer"
                      /\ serverResponses /= <<>>
                      /\ resp' = Head(serverResponses)
                      /\ serverResponses' = Tail(serverResponses)
                      /\ pc' = [pc EXCEPT ![Control] = "ControlDecide"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, authorized, 
                                      userTrash, binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      truckCommand, perm, req, scan, grant >>

ControlDecide == /\ pc[Control] = "ControlDecide"
                 /\ grant' = (resp.permission /\ TrashFitsCapacity(MaxUserTrash) /\  truckCommand.command = "emptied")
                 /\ IF grant'
                       THEN /\ pc' = [pc EXCEPT ![Control] = "ControlUnlock"]
                       ELSE /\ pc' = [pc EXCEPT ![Control] = "ControlDecline"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, authorized, userTrash, 
                                 binCommand, binSensor, scans, permissions, 
                                 serverRequests, serverResponses, truckCommand, 
                                 perm, req, scan, resp >>

ControlUnlock == /\ pc[Control] = "ControlUnlock"
                 /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
                 /\ pc' = [pc EXCEPT ![Control] = "ControlUnlockDone"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, authorized, userTrash, 
                                 binSensor, scans, permissions, serverRequests, 
                                 serverResponses, truckCommand, perm, req, 
                                 scan, resp, grant >>

ControlUnlockDone == /\ pc[Control] = "ControlUnlockDone"
                     /\ binCommand.command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "ControlGrant"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, authorized, 
                                     userTrash, binCommand, binSensor, scans, 
                                     permissions, serverRequests, 
                                     serverResponses, truckCommand, perm, req, 
                                     scan, resp, grant >>

ControlGrant == /\ pc[Control] = "ControlGrant"
                /\ permissions' = Append(permissions, ([user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]))
                /\ authorized' = TRUE
                /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitClose"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, serverRequests, 
                                serverResponses, truckCommand, perm, req, scan, 
                                resp, grant >>

ControlAwaitClose == /\ pc[Control] = "ControlAwaitClose"
                     /\ binSensor.sensor = "outer_door_closed"
                     /\ binSensor' = [sensor |-> "idle"]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitCloseDone"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, authorized, 
                                     userTrash, binCommand, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, req, scan, resp, 
                                     grant >>

ControlAwaitCloseDone == /\ pc[Control] = "ControlAwaitCloseDone"
                         /\ binCommand.command = "finished"
                         /\ pc' = [pc EXCEPT ![Control] = "ControlLock"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         authorized, userTrash, binCommand, 
                                         binSensor, scans, permissions, 
                                         serverRequests, serverResponses, 
                                         truckCommand, perm, req, scan, resp, 
                                         grant >>

ControlLock == /\ pc[Control] = "ControlLock"
               /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
               /\ pc' = [pc EXCEPT ![Control] = "ControlLockDone"]
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               authorized, userTrash, binSensor, scans, 
                               permissions, serverRequests, serverResponses, 
                               truckCommand, perm, req, scan, resp, grant >>

ControlLockDone == /\ pc[Control] = "ControlLockDone"
                   /\ binCommand.command = "finished"
                   /\ authorized' = FALSE
                   /\ pc' = [pc EXCEPT ![Control] = "ControlOpen"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binCommand, binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, req, scan, resp, grant >>

ControlOpen == /\ pc[Control] = "ControlOpen"
               /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
               /\ pc' = [pc EXCEPT ![Control] = "ControlOpenDone"]
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               authorized, userTrash, binSensor, scans, 
                               permissions, serverRequests, serverResponses, 
                               truckCommand, perm, req, scan, resp, grant >>

ControlOpenDone == /\ pc[Control] = "ControlOpenDone"
                   /\ binCommand.command = "finished"
                   /\ pc' = [pc EXCEPT ![Control] = "ControlExtendRam"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, authorized, 
                                   userTrash, binCommand, binSensor, scans, 
                                   permissions, serverRequests, 
                                   serverResponses, truckCommand, perm, req, 
                                   scan, resp, grant >>

ControlExtendRam == /\ pc[Control] = "ControlExtendRam"
                    /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlExtendRamDone"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, authorized, 
                                    userTrash, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scan, resp, grant >>

ControlExtendRamDone == /\ pc[Control] = "ControlExtendRamDone"
                        /\ binCommand.command = "finished"
                        /\ pc' = [pc EXCEPT ![Control] = "ControlRetractRam"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        authorized, userTrash, binCommand, 
                                        binSensor, scans, permissions, 
                                        serverRequests, serverResponses, 
                                        truckCommand, perm, req, scan, resp, 
                                        grant >>

ControlRetractRam == /\ pc[Control] = "ControlRetractRam"
                     /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlRetractRamDone"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, authorized, 
                                     userTrash, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, req, scan, resp, 
                                     grant >>

ControlRetractRamDone == /\ pc[Control] = "ControlRetractRamDone"
                         /\ binCommand.command = "finished"
                         /\ pc' = [pc EXCEPT ![Control] = "ControlClose"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         authorized, userTrash, binCommand, 
                                         binSensor, scans, permissions, 
                                         serverRequests, serverResponses, 
                                         truckCommand, perm, req, scan, resp, 
                                         grant >>

ControlClose == /\ pc[Control] = "ControlClose"
                /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
                /\ pc' = [pc EXCEPT ![Control] = "ControlCloseDone"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, authorized, userTrash, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, perm, req, scan, 
                                resp, grant >>

ControlCloseDone == /\ pc[Control] = "ControlCloseDone"
                    /\ binCommand.command = "finished"
                    /\ pc' = [pc EXCEPT ![Control] = "ControlTruck"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, authorized, 
                                    userTrash, binCommand, binSensor, scans, 
                                    permissions, serverRequests, 
                                    serverResponses, truckCommand, perm, req, 
                                    scan, resp, grant >>

ControlDecline == /\ pc[Control] = "ControlDecline"
                  /\ permissions' = Append(permissions, ([user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]))
                  /\ pc' = [pc EXCEPT ![Control] = "ControlTruck"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, authorized, userTrash, 
                                  binCommand, binSensor, scans, serverRequests, 
                                  serverResponses, truckCommand, perm, req, 
                                  scan, resp, grant >>

ControlTruck == /\ pc[Control] = "ControlTruck"
                /\ IF ~TrashFitsCapacity(MaxUserTrash) /\ truckCommand.command = "emptied"
                      THEN /\ truckCommand' = [command  |-> "request", bin |-> 1]
                      ELSE /\ TRUE
                           /\ UNCHANGED truckCommand
                /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, authorized, userTrash, 
                                binCommand, binSensor, scans, permissions, 
                                serverRequests, serverResponses, perm, req, 
                                scan, resp, grant >>

controlProcess == ControlStart \/ ControllerAwaitScan \/ ControlAskServer
                     \/ ControlAwaitServer \/ ControlDecide
                     \/ ControlUnlock \/ ControlUnlockDone \/ ControlGrant
                     \/ ControlAwaitClose \/ ControlAwaitCloseDone
                     \/ ControlLock \/ ControlLockDone \/ ControlOpen
                     \/ ControlOpenDone \/ ControlExtendRam
                     \/ ControlExtendRamDone \/ ControlRetractRam
                     \/ ControlRetractRamDone \/ ControlClose
                     \/ ControlCloseDone \/ ControlDecline \/ ControlTruck

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Oct 20 11:48:36 CEST 2026 by erinrobinson
