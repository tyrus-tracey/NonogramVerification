include "PuzzleLine.dfy"
include "Puzzle.dfy"

class Solver
{
    var Lines: array<Line>
    var Puzzle: Puzzle

    constructor(puzzle: Puzzle)
    {
        Puzzle := puzzle;
    }

    method GetTotalSolved() returns (total: int)
    {
        total := 0;
        var cellKey: int;

        for cellKey := 0 to this.Puzzle.Cells.Length
        {
            if (this.Puzzle.Cells[cellKey].AISolution != NULL)
            {
                total := total + 1;
            }
        }
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