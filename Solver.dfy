include "PuzzleLine.dfy"
include "Puzzle.dfy"

class Solver
{
    var Lines: array<PuzzleLine>
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

    method FindCompletedSections(line: PuzzleLine)
    requires line in Lines[..]
    ensures this.Lines == old(this.Lines)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>  
        this.Lines[j].Cells == old(this.Lines[j].Cells)
    modifies 
        line,
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n]
    {
        for sectionKey: int := 0 to line.Sections.Length
        invariant 0 <= sectionKey <= line.Sections.Length
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Cells == old(this.Lines[i].Cells) &&
                this.Lines[i].Sections == old(this.Lines[i].Sections)
        {
            var section := line.Sections[sectionKey];

            if (!section.Solved && section.PossibleStartIndexes.Length == 1)
            {
                var firstNegative := section.PossibleStartIndexes[0] - 1;
                var lastNegative := section.PossibleStartIndexes[0] + section.Length;

                if (0 <= firstNegative < |line.Cells| && line.Cells[firstNegative].AISolution == CellValue.NULL)
                {
                    SetCellSolution(line.Cells[firstNegative], CellValue.0);
                }
            }
        }
    }

    method FindCompletedLines(line: PuzzleLine)
    requires line in Lines[..]
    ensures this.Lines == old(this.Lines)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>  
        this.Lines[j].Cells == old(this.Lines[j].Cells)
    modifies 
        line,
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n]
    {
        var totalSectionLength: int := 0;
        var totalPositiveSolved: int := 0;

        for sectionKey: int := 0 to line.Sections.Length
        invariant 0 <= sectionKey <= line.Sections.Length
        {
            var section := line.Sections[sectionKey];
            totalSectionLength := totalSectionLength + section.Length;
        }

        for cellKey: int := 0 to |line.Cells|
        invariant 0 <= cellKey <= |line.Cells|
        {
            var cell := line.Cells[cellKey];
            if (cell.AISolution == CellValue.1)
            {
                totalPositiveSolved := totalPositiveSolved + 1;
            }
        }

        if (totalSectionLength == totalPositiveSolved)
        {
            for cellKey: int := 0 to |line.Cells|
            invariant 0 <= cellKey <= |line.Cells|
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Cells == old(this.Lines[i].Cells)
            {
                var cell := line.Cells[cellKey];
                if (cell.AISolution == CellValue.NULL)
                {
                    SetCellSolution(cell, CellValue.0);
                }
            }
        }
    }

    // Propogates PuzzleCell value to all row/column Lines it belongs to.
    // If this solves a PuzzleLine, marks the PuzzleLine as solved.
    method SetCellSolution(puzzleCell: PuzzleCell, value: CellValue)
    ensures this.Lines == old(this.Lines)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>  
        this.Lines[j].Cells == old(this.Lines[j].Cells) &&
        this.Lines[j].Sections == old(this.Lines[j].Sections)
    modifies 
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n]
    {
        var lineKey: int, cellKey: int, cellsSolved: int;
        var line : PuzzleLine;
        var isRow:bool , isCol: bool;
        var cell : PuzzleCell;

        for lineKey := 0 to this.Lines.Length
        invariant 0 <= lineKey <= this.Lines.Length
        invariant forall i:int :: 0 <= i < this.Lines.Length ==>
            this.Lines[i].Cells == old(this.Lines[i].Cells) &&
            this.Lines[i].Sections == old(this.Lines[i].Sections)
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