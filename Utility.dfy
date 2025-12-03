include "PuzzleLine.dfy"

class Utility {

    //remove a nat from an array of nats
    method RemoveFromArray(source: array<nat>, key: nat) returns (copy: array<nat>)
    requires source.Length > 1
    requires key < source.Length
    ensures copy.Length == source.Length - 1
    ensures forall i: nat :: 0 <= i < key ==> source[i] == copy[i]
    ensures forall j: nat :: source.Length > j > key ==> source[j] == copy[j-1]
    {
        copy := new nat[source.Length - 1];
        for i: nat := 0 to key
        invariant 0 <= i <= key
        invariant forall k: nat :: 0 <= k < i ==> source[k] == copy[k]
        {
            copy[i] := source[i];
            
        }

        for j: nat := key + 1 to source.Length
        invariant key + 1 <= j <= source.Length
        invariant forall k: nat :: key+1 <= k < j ==> source[k] == copy[k-1]
        {
            copy[j-1] := source[j];
        }

        return copy;
    }

    method CloneArray(a: array<nat>) returns (copy: array<nat>) 
    ensures copy.Length == a.Length
    ensures forall j: nat :: 0 <= j < a.Length ==> copy[j] == a[j]
    {
        copy := new nat[a.Length];
        for i: nat := 0 to a.Length 
        invariant 0 <= i <= a.Length
        invariant forall j: nat :: 0 <= j < i ==> copy[j] == a[j]
        {
            copy[i] := a[i];
        }

        return copy;
    }

    method FindLongestSection(a: array<Section>) returns (index: nat)
    requires a.Length > 0
    ensures index < a.Length && forall j: int :: 0 <= j < a.Length ==> a[j].Length <= a[index].Length
    {
        index := 0;
        for i: nat := 0 to a.Length 
        invariant 0 <= index < a.Length
        invariant forall j: int :: 0 <= j < i ==> a[j].Length <= a[index].Length
        {
            if a[i].Length > a[index].Length {
                index := i;
            }
        }

        return index;
    }

    method PushToArray(a: array<Chain>, chain: Chain) returns (result: array<Chain>)
    ensures result.Length == a.Length + 1
    {
        
    }
}