---- MODULE manager ----
EXTENDS TLC
CONSTANT M \* managers in the system

(*--
algorithm manager {
variable chan = [n \in 1..M: n -> <<>>];


process manager = "Manager"

varibles backup = <<1,2,3,4,5,6>>;

S1: {
    while backup # <<>>{
        
        either{
            front := Head(backup);
            rest := Tail(backup);
        } 
        or {
            skip;
            
        }
    }
}



}
*)
====