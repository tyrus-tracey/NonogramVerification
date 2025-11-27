datatype CellValue = NULL | 0 | 1

class PuzzleCell
{
    var Index: int
    var Column: int
    var Row: int
    var Solution: CellValue
    var UserSolution: CellValue
    var AISolution: CellValue

    method SetAISolution(solution: CellValue)
    modifies this
    ensures AISolution == solution
    {
        AISolution := solution;
    }

    constructor ()
    {
        Index := 0;
        Column := 0;
        Row := 0;
        Solution := NULL;
        UserSolution := NULL;
        AISolution := NULL;
    }
}


class Line 
{
    var Type: string
    var Index: int
    var Length: int
    var MinimumSectionLength: int
    var Sections: array<array<int>>
    var Cells: seq<PuzzleCell>
    var Solved: bool

    constructor()
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

class Solver
{
    var Lines: array<Line>
    constructor()
    {
        //TODO
    }

    // Propogates PuzzleCell value to all row/column Lines it belongs to.
    // If this solves a Line, marks the Line as solved.
    method SetCellSolution(puzzleCell: PuzzleCell, value: CellValue)
    requires this.Lines.Length > 0
    requires forall j:int :: 0 <= j < this.Lines.Length ==> 
        |this.Lines[j].Cells| > 0
    ensures this.Lines == old(this.Lines)
    modifies 
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n]
    {
        var lineKey: int, cellKey: int, cellsSolved: int;
        var line : Line;
        var isRow:bool , isCol: bool;
        var cell : PuzzleCell;

        for lineKey := 0 to this.Lines.Length
        invariant 0 <= lineKey <= this.Lines.Length
        invariant forall i:int :: 0 <= i < this.Lines.Length ==>
            this.Lines[i].Cells == old(this.Lines[i].Cells)
        {   
            line := this.Lines[lineKey];
            isRow := line.Type == "row" && line.Index == puzzleCell.Row;
            isCol := line.Type == "column" && line.Index == puzzleCell.Column;
            cellsSolved := 0;

            if (isRow || isCol)
            {
                line.UpdateCells(puzzleCell, value);
            }
        }
    }
}

