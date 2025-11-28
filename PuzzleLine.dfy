include "PuzzleCell.dfy"

class PuzzleLine
{
    var Type: string
    var Index: int
    var Length: int
    var MinimumSectionLength: int
    var Sections: array<Section>
    var Cells: seq<PuzzleCell>
    var Solved: bool

    constructor()
    ensures fresh(this.Cells)
    {
        var cell: PuzzleCell := new PuzzleCell();
        Type := "";
        Index := 0;
        Length := 0;
        MinimumSectionLength := 0;
        Cells := [cell, cell, cell, cell, cell];
        Solved := false;
    }

    method SetSolveState(state: bool)
    modifies this`Solved
    ensures Solved == state
    {
        Solved := state;
    }
    
    method UpdateCells(puzzleCell: PuzzleCell, value: CellValue)
    modifies this`Solved, this.Cells[..]
    ensures this.Sections == old(this.Sections)
    {
        var cellsSolved : int := 0;

        for cellKey : int := 0 to |this.Cells|
        invariant 0 <= cellKey <= |this.Cells|
        invariant this.Cells == old(this.Cells)
        {
            var cell : PuzzleCell := this.Cells[cellKey];
            if (cell.Index == puzzleCell.Index) {
                cell.SetAISolution(value);
                cellsSolved := cellsSolved + 1;
            } else if (cell.AISolution == NULL) {
                cellsSolved := cellsSolved + 1;
            }
        }
        
        SetSolveState(true);
    }
}

class Section
{
    var Index: int
    var Length: int
    var PossibleStartIndexes: array<int>
    var KnownIndexes: array<int>
    var Solved: bool

    constructor(Index: int, Length: int, PossibleStartIndexes: array<int>, KnownIndexes: array<int>)
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
    var Start: int
    var Length: int

    constructor(Start: int, Length: int)
    ensures this.Start == Start && this.Length == Length
    {
        this.Start := Start;
        this.Length := Length;
    }
}