include "PuzzleCell.dfy"

class PuzzleLine
{
    var Type: string
    var Index: nat
    var Length: nat
    var MinimumSectionLength: nat
    var Sections: array<Section>
    var Cells: seq<PuzzleCell>
    var Solved: bool

    constructor()
    ensures fresh(this.Cells) && Valid()
    {
        var cell: PuzzleCell := new PuzzleCell();
        Type := "";
        Index := 0;
        Length := 5;
        MinimumSectionLength := 0;
        Sections := new Section[0];
        Cells := [cell, cell, cell, cell, cell];
        Solved := false;
    }

    method SetSolveState(state: bool)
    requires Valid() && state == true
    modifies this`Solved
    ensures Solved == true && Valid()
    {
        Solved := state;
    }
    
    method UpdateCells(puzzleCell: PuzzleCell, value: CellValue)
    requires Valid() && value != CellValue.NULL
    modifies this`Solved, this.Cells[..]
    ensures this.Cells == old(this.Cells) && this.Sections == old(this.Sections) && Valid()
    ensures forall j:int :: 0 <= j < |this.Cells| ==>
            old(this.Cells[j].AISolution) != CellValue.NULL ==> 
            this.Cells[j].AISolution != CellValue.NULL
    {
        var cellsSolved : int := 0;

        for cellKey : int := 0 to |this.Cells|
        invariant 0 <= cellKey <= |this.Cells|
        invariant this.Cells == old(this.Cells)
        invariant forall j:int :: 0 <= j < |this.Cells| ==>
            old(this.Cells[j].AISolution) != CellValue.NULL ==> 
            this.Cells[j].AISolution != CellValue.NULL
        {
            var cell : PuzzleCell := this.Cells[cellKey];
            if (cell.Index == puzzleCell.Index) {
                cell.SetAISolution(value);
                cellsSolved := cellsSolved + 1;
            } else if (cell.AISolution == CellValue.NULL) {
                cellsSolved := cellsSolved + 1;
            }
        }
        
        SetSolveState(true);
    }

    ghost predicate Valid()
    reads *
    // something more like one of these is the sort of reads clause I actually want
    // but it gives a message that set comprehensions in predicates cannot depend on references
    // so not sure if there's any way of getting this approach to work
    /*
        set c | exists m,n ::
            0 <= m < this.Sections.Length &&
            0 <= n < this.Sections[m].PossibleStartIndexes.Length &&
            c == this.Sections[m].PossibleStartIndexes
        set c | exists m ::
            0 <= m < this.Sections.Length &&
            c == this.Sections[m]
    */
    {
        Length == |Cells| &&
        forall i: int :: 0 <= i < this.Sections.Length ==>
        forall j: int :: 0 <= j < this.Sections[i].PossibleStartIndexes.Length ==>
            0 <= this.Sections[i].PossibleStartIndexes[j] + this.Sections[i].Length < this.Length
    }
}

class Section
{
    var Index: nat
    var Length: nat
    var PossibleStartIndexes: array<nat>
    var KnownIndexes: array<nat>
    var Solved: bool

    constructor(Index: nat, Length: nat, PossibleStartIndexes: array<nat>, KnownIndexes: array<nat>)
    ensures this.Index == Index &&
        this.Length == Length &&
        this.PossibleStartIndexes == PossibleStartIndexes &&
        this.KnownIndexes == KnownIndexes &&
        this.Solved == false
    {
        this.Index := Index;
        this.Length := Length;
        this.PossibleStartIndexes := PossibleStartIndexes;
        this.KnownIndexes := KnownIndexes;
        this.Solved := false;
    }
}

class Chain
{
    var Start: nat
    var Length: nat

    constructor(Start: nat, Length: nat)
    ensures this.Start == Start && this.Length == Length
    {
        this.Start := Start;
        this.Length := Length;
    }
}