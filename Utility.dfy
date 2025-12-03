include "PuzzleLine.dfy"

class Utility {

    //remove a nat from an array of nats
    method RemoveFromArray(source: array<nat>, value: nat) returns (copy: array<nat>)
    requires source.Length > 1
    ensures copy.Length == source.Length - 1
    {
        copy := new nat[source.Length - 1];
        var copyIndex: nat := 0;
        for i: nat := 0 to source.Length 
        invariant 0 <= copyIndex <= copy.Length
        {
            if(source[i] != value) {
                copy[copyIndex] := source[i];
                copyIndex := copyIndex + 1;
            }
        }
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
}