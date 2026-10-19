--------------------------- MODULE trash_multiple ---------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bins
  outerDoorOpen = [b \in Bins |-> FALSE],
  outerDoorLocked = [b \in Bins |-> TRUE],
  trapDoorOpen = [b \in Bins |-> FALSE],
  ramExtended = [b \in Bins |-> FALSE],
  trashInTop = [b \in Bins |-> 0],
  trashCompressed = [b \in Bins |-> 0],
  trashUncompressed = [b \in Bins |-> 0],
  trashCapacity = [b \in Bins |-> MaxCapacity],
  trapDestroyed = [b \in Bins |-> FALSE],

  \* Variables for users
  userTrash = [u \in Users |-> 0],

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
  \* Sensor from outer door of bin
  binSensor = [b \in Bins |-> [sensor |-> "idle"]],
  grantedUser = [b \in Bins |-> 0],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = [u \in Users |-> << >>],
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Commands for the trucks
  truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
\* Trucks currently idle
AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}
BinBusy(b) == \E t \in Trucks: truckCommand[t].command /= "emptied"
                               /\ truckCommand[t].bin = b
BinFull(b) == ~TrashFitsCapacity(b, MaxUserTrash)
\* Bins needing truck
BinsNeedingTruck == {b \in Bins : BinFull(b) /\ ~BinBusy(b)}

\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.
\* Make sure your formalisations hold for every bin/user, not just one specific instance.

\* For each trash bin, the outer door can only be locked if it is closed.
OuterDoorLocked == \A b \in Bins: outerDoorLocked[b] => ~outerDoorOpen[b]
\* For each trash bin, the vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == \A b \in Bins: ramExtended[b] => (outerDoorLocked[b] /\ ~outerDoorOpen[b])
\* For each trash bin, every time it is full, it is eventually not full anymore.
TrashEmptied == \A b \in Bins: BinFull(b) ~> ~BinFull(b)
\* No unauthorized user can open the outer door of any trash bin.
AuthorizedOpenOnly == \A b \in Bins: outerDoorOpen[b] => grantedUser[b] \in Users
\* Each user infinitely often has trash and infinitely often has no trash.
UserTrash == \A u \in Users: []<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0)
\* For each user, every time they have trash they can deposit their trash.
UserTrashDeposited == \A u \in Users: (userTrash[u] > 0) ~> (userTrash[u] = 0)
\* For each trash bin, every time a truck is requested for it, a truck has eventually emptied it.
TruckEmpties == \A b \in Bins: BinBusy(b) ~> ~BinBusy(b)

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
      await binCommand[self].command /= "finished";
      if binCommand[self].command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked[self];
        outerDoorOpen[self] := binCommand[self].open;
        if ~outerDoorOpen[self] then
          binSensor[self] := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand[self].command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen[self];
        outerDoorLocked[self] := ~(binCommand[self].open);
      elsif binCommand[self].command = "change_trap_door" then
        assert outerDoorLocked[self];
        \* Open/Close trap door
        if ramExtended[self] \/ CapacityExceeded(self) then
            trapDestroyed[self] := TRUE;
        end if;
        trapDoorOpen[self] := binCommand[self].open;
        if trapDoorOpen[self] then
          \* Trash falls through
          trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
          trashInTop[self] := 0;
        end if
      elsif binCommand[self].command = "change_ram" then
        assert outerDoorLocked[self];
        \* Extend/Retract ram
        ramExtended[self] := binCommand[self].open;
        if ramExtended[self] then
          if ~trapDoorOpen[self] then
            trapDestroyed[self] := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed[self], trashUncompressed[self]);
        end if;
      elsif binCommand[self].command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked[self];
        assert ~trapDoorOpen[self];
        assert ~ramExtended[self];
        assert trashInTop[self] = 0;
        assert trashUncompressed[self] = 0;
        trashCompressed[self] := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand[self].command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
      \* Non-deterministically choose a bin
      with sBin \in Bins do
        selectedBin := sBin;
        write(scans, [user |-> self, bin |-> selectedBin]);
      end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
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
\* Remodel it to react to requests and empty the requested trash bin!
fair process truckProcess \in Trucks
begin
  TruckStart:
    \* Implement behaviour
    \* Request the trash bin
    while TRUE do
        \* React to a request from the main controller
        TruckAwaitRequest:
        await truckCommand[self].command = "request";
        \* Drive to the trash bin
        TruckDrive:
        truckCommand[self] := [truckCommand[self] EXCEPT !.command = "arrived"];
        \* empty trash bin by sending "empty"
        TruckEmpty:
        binCommand[truckCommand[self].bin] := [command |-> "empty", open |-> FALSE];
        TruckEmptyDone:
        await binCommand[truckCommand[self].bin].command = "finished";
        \* the truck informs the main control process that the bin is emptied
        TruckReport:
        truckCommand[self] := [command |-> "emptied", bin |-> truckCommand[self].bin];
        \* awaits for new requests
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* DUMMY main control process type.
\* Remodel it to control all trash bins in the system and handle requests by users!
fair process controlProcess = Control
variables
  scan = [user |-> 0, bin |-> 1],
  resp = [user |-> 0, permission |-> FALSE],
  grant = FALSE
begin
  ControlStart:
    \* Implement behaviour
    \* When a trash bin needs to be emptied
    \* which of the available trucks should be requested for which bin
    while TRUE do
    ControllerAwaitScan:
      read(scans, scan);
    ControlAskServer:
      write(serverRequests, [user |-> scan.user]);
    ControlAwaitServer:
      read(serverResponses, resp);
    \* Check the capacity of the bin
    ControlDecide:
      grant := resp.permission /\ TrashFitsCapacity(scan.bin, MaxUserTrash) /\  ~BinBusy(scan.bin);
      if grant then
        ControlUnlock:
          binCommand[scan.bin] := [command |-> "change_outer_lock", open |-> TRUE];
        ControlUnlockDone:
          await binCommand[scan.bin].command = "finished";
        \* Permission is either answered or declined
        ControlGrant:
          write(permissions[scan.user], [user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]);
          grantedUser[scan.bin] := scan.user;
        \* If the request is granted, check if the outer door is closed
        ControlAwaitClose:
          await binSensor[scan.bin].sensor = "outer_door_closed";
          binSensor[scan.bin] := [sensor |-> "idle"];
        ControlAwaitCloseDone:
          await binCommand[scan.bin].command = "finished";
        ControlLock:
          binCommand[scan.bin] := [command |-> "change_outer_lock", open |-> FALSE];
        ControlLockDone:
          await binCommand[scan.bin].command = "finished";
          grantedUser[scan.bin] := 0;
        \* Move the deposited trash into the main compartment of the trash bin 
        ControlOpen:
          binCommand[scan.bin] := [command |-> "change_trap_door", open |-> TRUE];
        \* The ram should only be extended if the trap door is open
        ControlOpenDone:
          await binCommand[scan.bin].command = "finished";
        \* operate the ram
        ControlExtendRam:
          binCommand[scan.bin] := [command |-> "change_ram", open |-> TRUE];
        ControlExtendRamDone:
          await binCommand[scan.bin].command = "finished";
        ControlRetractRam:
          binCommand[scan.bin] := [command |-> "change_ram", open |-> FALSE];
        ControlRetractRamDone:
          await binCommand[scan.bin].command = "finished";
        ControlClose:
          binCommand[scan.bin] := [command |-> "change_trap_door", open |-> FALSE];
        ControlCloseDone:
          await binCommand[scan.bin].command = "finished";
      else
        ControlDecline:
          write(permissions[scan.user], [user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]);
      end if;
    ControlTruck:
        if BinsNeedingTruck /= {} /\ AvailableTrucks /= {} then
          with b \in BinsNeedingTruck, t \in AvailableTrucks do
            truckCommand[t] := [command |-> "request", bin |-> b];
          end with;
        end if;
  end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8e025d66" /\ chksum(tla) = "6a6e8f7")
VARIABLES pc, outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, grantedUser, scans, 
          permissions, serverRequests, serverResponses, truckCommand

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]

AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}
BinBusy(b) == \E t \in Trucks: truckCommand[t].command /= "emptied"
                               /\ truckCommand[t].bin = b
BinFull(b) == ~TrashFitsCapacity(b, MaxUserTrash)

BinsNeedingTruck == {b \in Bins : BinFull(b) /\ ~BinBusy(b)}





TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins


MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)









OuterDoorLocked == \A b \in Bins: outerDoorLocked[b] => ~outerDoorOpen[b]

RamOuterDoor == \A b \in Bins: ramExtended[b] => (outerDoorLocked[b] /\ ~outerDoorOpen[b])

TrashEmptied == \A b \in Bins: BinFull(b) ~> ~BinFull(b)

AuthorizedOpenOnly == \A b \in Bins: outerDoorOpen[b] => grantedUser[b] \in Users

UserTrash == \A u \in Users: []<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0)

UserTrashDeposited == \A u \in Users: (userTrash[u] > 0) ~> (userTrash[u] = 0)

TruckEmpties == \A b \in Bins: BinBusy(b) ~> ~BinBusy(b)

VARIABLES perm, selectedBin, req, scan, resp, grant

vars == << pc, outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, grantedUser, 
           scans, permissions, serverRequests, serverResponses, truckCommand, 
           perm, selectedBin, req, scan, resp, grant >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ userTrash = [u \in Users |-> 0]
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ grantedUser = [b \in Bins |-> 0]
        /\ scans = << >>
        /\ permissions = [u \in Users |-> << >>]
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
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
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 175, column 9.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 182, column 9.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 185, column 9.")
                                                            /\ IF ramExtended[self] \/ CapacityExceeded(self)
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 197, column 9.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 209, column 9.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 210, column 9.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 211, column 9.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 212, column 9.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 213, column 9.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 217, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           binCommand, grantedUser, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, scan, resp, grant >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, grantedUser, scans, 
                                            permissions, serverRequests, 
                                            serverResponses, truckCommand, 
                                            perm, selectedBin, req, scan, resp, 
                                            grant >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, grantedUser, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, scan, resp, grant >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E sBin \in Bins:
                           /\ selectedBin' = [selectedBin EXCEPT ![self] = sBin]
                           /\ scans' = Append(scans, ([user |-> self, bin |-> selectedBin'[self]]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, grantedUser, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, req, 
                                      scan, resp, grant >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 249, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 250, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, grantedUser, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, selectedBin, req, 
                                               scan, resp, grant >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, grantedUser, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, 
                                      selectedBin, req, scan, resp, grant >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, grantedUser, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, scan, resp, grant >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 257, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, grantedUser, 
                                          scans, permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          selectedBin, req, scan, resp, grant >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, grantedUser, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       selectedBin, req, scan, resp, grant >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, 
                                             grantedUser, scans, permissions, 
                                             serverRequests, serverResponses, 
                                             truckCommand, perm, selectedBin, 
                                             req, scan, resp, grant >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, grantedUser, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, 
                                      selectedBin, req, scan, resp, grant >>

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
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, grantedUser, 
                                       scans, permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       selectedBin, req, scan, resp, grant >>

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
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, grantedUser, 
                                      scans, permissions, truckCommand, perm, 
                                      selectedBin, scan, resp, grant >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ pc' = [pc EXCEPT ![self] = "TruckAwaitRequest"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, grantedUser, scans, 
                                    permissions, serverRequests, 
                                    serverResponses, truckCommand, perm, 
                                    selectedBin, req, scan, resp, grant >>

TruckAwaitRequest(self) == /\ pc[self] = "TruckAwaitRequest"
                           /\ truckCommand[self].command = "request"
                           /\ pc' = [pc EXCEPT ![self] = "TruckDrive"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, grantedUser, 
                                           scans, permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, scan, resp, grant >>

TruckDrive(self) == /\ pc[self] = "TruckDrive"
                    /\ truckCommand' = [truckCommand EXCEPT ![self] = [truckCommand[self] EXCEPT !.command = "arrived"]]
                    /\ pc' = [pc EXCEPT ![self] = "TruckEmpty"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, grantedUser, scans, 
                                    permissions, serverRequests, 
                                    serverResponses, perm, selectedBin, req, 
                                    scan, resp, grant >>

TruckEmpty(self) == /\ pc[self] = "TruckEmpty"
                    /\ binCommand' = [binCommand EXCEPT ![truckCommand[self].bin] = [command |-> "empty", open |-> FALSE]]
                    /\ pc' = [pc EXCEPT ![self] = "TruckEmptyDone"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, grantedUser, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, scan, 
                                    resp, grant >>

TruckEmptyDone(self) == /\ pc[self] = "TruckEmptyDone"
                        /\ binCommand[truckCommand[self].bin].command = "finished"
                        /\ pc' = [pc EXCEPT ![self] = "TruckReport"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        grantedUser, scans, permissions, 
                                        serverRequests, serverResponses, 
                                        truckCommand, perm, selectedBin, req, 
                                        scan, resp, grant >>

TruckReport(self) == /\ pc[self] = "TruckReport"
                     /\ truckCommand' = [truckCommand EXCEPT ![self] = [command |-> "emptied", bin |-> truckCommand[self].bin]]
                     /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, grantedUser, scans, 
                                     permissions, serverRequests, 
                                     serverResponses, perm, selectedBin, req, 
                                     scan, resp, grant >>

truckProcess(self) == TruckStart(self) \/ TruckAwaitRequest(self)
                         \/ TruckDrive(self) \/ TruckEmpty(self)
                         \/ TruckEmptyDone(self) \/ TruckReport(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ pc' = [pc EXCEPT ![Control] = "ControllerAwaitScan"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, grantedUser, scans, permissions, 
                                serverRequests, serverResponses, truckCommand, 
                                perm, selectedBin, req, scan, resp, grant >>

ControllerAwaitScan == /\ pc[Control] = "ControllerAwaitScan"
                       /\ scans /= <<>>
                       /\ scan' = Head(scans)
                       /\ scans' = Tail(scans)
                       /\ pc' = [pc EXCEPT ![Control] = "ControlAskServer"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, grantedUser, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       selectedBin, req, resp, grant >>

ControlAskServer == /\ pc[Control] = "ControlAskServer"
                    /\ serverRequests' = Append(serverRequests, ([user |-> scan.user]))
                    /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitServer"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, grantedUser, scans, 
                                    permissions, serverResponses, truckCommand, 
                                    perm, selectedBin, req, scan, resp, grant >>

ControlAwaitServer == /\ pc[Control] = "ControlAwaitServer"
                      /\ serverResponses /= <<>>
                      /\ resp' = Head(serverResponses)
                      /\ serverResponses' = Tail(serverResponses)
                      /\ pc' = [pc EXCEPT ![Control] = "ControlDecide"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, grantedUser, 
                                      scans, permissions, serverRequests, 
                                      truckCommand, perm, selectedBin, req, 
                                      scan, grant >>

ControlDecide == /\ pc[Control] = "ControlDecide"
                 /\ grant' = (resp.permission /\ TrashFitsCapacity(scan.bin, MaxUserTrash) /\  ~BinBusy(scan.bin))
                 /\ IF grant'
                       THEN /\ pc' = [pc EXCEPT ![Control] = "ControlUnlock"]
                       ELSE /\ pc' = [pc EXCEPT ![Control] = "ControlDecline"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binCommand, 
                                 binSensor, grantedUser, scans, permissions, 
                                 serverRequests, serverResponses, truckCommand, 
                                 perm, selectedBin, req, scan, resp >>

ControlUnlock == /\ pc[Control] = "ControlUnlock"
                 /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_outer_lock", open |-> TRUE]]
                 /\ pc' = [pc EXCEPT ![Control] = "ControlUnlockDone"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, 
                                 grantedUser, scans, permissions, 
                                 serverRequests, serverResponses, truckCommand, 
                                 perm, selectedBin, req, scan, resp, grant >>

ControlUnlockDone == /\ pc[Control] = "ControlUnlockDone"
                     /\ binCommand[scan.bin].command = "finished"
                     /\ pc' = [pc EXCEPT ![Control] = "ControlGrant"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, grantedUser, scans, 
                                     permissions, serverRequests, 
                                     serverResponses, truckCommand, perm, 
                                     selectedBin, req, scan, resp, grant >>

ControlGrant == /\ pc[Control] = "ControlGrant"
                /\ permissions' = [permissions EXCEPT ![scan.user] = Append((permissions[scan.user]), ([user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]))]
                /\ grantedUser' = [grantedUser EXCEPT ![scan.bin] = scan.user]
                /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitClose"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, serverRequests, 
                                serverResponses, truckCommand, perm, 
                                selectedBin, req, scan, resp, grant >>

ControlAwaitClose == /\ pc[Control] = "ControlAwaitClose"
                     /\ binSensor[scan.bin].sensor = "outer_door_closed"
                     /\ binSensor' = [binSensor EXCEPT ![scan.bin] = [sensor |-> "idle"]]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitCloseDone"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, grantedUser, scans, 
                                     permissions, serverRequests, 
                                     serverResponses, truckCommand, perm, 
                                     selectedBin, req, scan, resp, grant >>

ControlAwaitCloseDone == /\ pc[Control] = "ControlAwaitCloseDone"
                         /\ binCommand[scan.bin].command = "finished"
                         /\ pc' = [pc EXCEPT ![Control] = "ControlLock"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, binCommand, binSensor, 
                                         grantedUser, scans, permissions, 
                                         serverRequests, serverResponses, 
                                         truckCommand, perm, selectedBin, req, 
                                         scan, resp, grant >>

ControlLock == /\ pc[Control] = "ControlLock"
               /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_outer_lock", open |-> FALSE]]
               /\ pc' = [pc EXCEPT ![Control] = "ControlLockDone"]
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, binSensor, grantedUser, scans, 
                               permissions, serverRequests, serverResponses, 
                               truckCommand, perm, selectedBin, req, scan, 
                               resp, grant >>

ControlLockDone == /\ pc[Control] = "ControlLockDone"
                   /\ binCommand[scan.bin].command = "finished"
                   /\ grantedUser' = [grantedUser EXCEPT ![scan.bin] = 0]
                   /\ pc' = [pc EXCEPT ![Control] = "ControlOpen"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binCommand, binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, selectedBin, req, scan, 
                                   resp, grant >>

ControlOpen == /\ pc[Control] = "ControlOpen"
               /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_trap_door", open |-> TRUE]]
               /\ pc' = [pc EXCEPT ![Control] = "ControlOpenDone"]
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, binSensor, grantedUser, scans, 
                               permissions, serverRequests, serverResponses, 
                               truckCommand, perm, selectedBin, req, scan, 
                               resp, grant >>

ControlOpenDone == /\ pc[Control] = "ControlOpenDone"
                   /\ binCommand[scan.bin].command = "finished"
                   /\ pc' = [pc EXCEPT ![Control] = "ControlExtendRam"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binCommand, binSensor, grantedUser, scans, 
                                   permissions, serverRequests, 
                                   serverResponses, truckCommand, perm, 
                                   selectedBin, req, scan, resp, grant >>

ControlExtendRam == /\ pc[Control] = "ControlExtendRam"
                    /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_ram", open |-> TRUE]]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlExtendRamDone"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, grantedUser, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, scan, 
                                    resp, grant >>

ControlExtendRamDone == /\ pc[Control] = "ControlExtendRamDone"
                        /\ binCommand[scan.bin].command = "finished"
                        /\ pc' = [pc EXCEPT ![Control] = "ControlRetractRam"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        grantedUser, scans, permissions, 
                                        serverRequests, serverResponses, 
                                        truckCommand, perm, selectedBin, req, 
                                        scan, resp, grant >>

ControlRetractRam == /\ pc[Control] = "ControlRetractRam"
                     /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_ram", open |-> FALSE]]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlRetractRamDone"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binSensor, grantedUser, scans, 
                                     permissions, serverRequests, 
                                     serverResponses, truckCommand, perm, 
                                     selectedBin, req, scan, resp, grant >>

ControlRetractRamDone == /\ pc[Control] = "ControlRetractRamDone"
                         /\ binCommand[scan.bin].command = "finished"
                         /\ pc' = [pc EXCEPT ![Control] = "ControlClose"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, binCommand, binSensor, 
                                         grantedUser, scans, permissions, 
                                         serverRequests, serverResponses, 
                                         truckCommand, perm, selectedBin, req, 
                                         scan, resp, grant >>

ControlClose == /\ pc[Control] = "ControlClose"
                /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_trap_door", open |-> FALSE]]
                /\ pc' = [pc EXCEPT ![Control] = "ControlCloseDone"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binSensor, 
                                grantedUser, scans, permissions, 
                                serverRequests, serverResponses, truckCommand, 
                                perm, selectedBin, req, scan, resp, grant >>

ControlCloseDone == /\ pc[Control] = "ControlCloseDone"
                    /\ binCommand[scan.bin].command = "finished"
                    /\ pc' = [pc EXCEPT ![Control] = "ControlTruck"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, grantedUser, scans, 
                                    permissions, serverRequests, 
                                    serverResponses, truckCommand, perm, 
                                    selectedBin, req, scan, resp, grant >>

ControlDecline == /\ pc[Control] = "ControlDecline"
                  /\ permissions' = [permissions EXCEPT ![scan.user] = Append((permissions[scan.user]), ([user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]))]
                  /\ pc' = [pc EXCEPT ![Control] = "ControlTruck"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, 
                                  binSensor, grantedUser, scans, 
                                  serverRequests, serverResponses, 
                                  truckCommand, perm, selectedBin, req, scan, 
                                  resp, grant >>

ControlTruck == /\ pc[Control] = "ControlTruck"
                /\ IF BinsNeedingTruck /= {} /\ AvailableTrucks /= {}
                      THEN /\ \E b \in BinsNeedingTruck:
                                \E t \in AvailableTrucks:
                                  truckCommand' = [truckCommand EXCEPT ![t] = [command |-> "request", bin |-> b]]
                      ELSE /\ TRUE
                           /\ UNCHANGED truckCommand
                /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, grantedUser, scans, permissions, 
                                serverRequests, serverResponses, perm, 
                                selectedBin, req, scan, resp, grant >>

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
