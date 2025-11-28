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
            if (this.Puzzle.Cells[cellKey].AISolution != CellValue.NULL)
            {
                total := total + 1;
            }
        }
    }

    method FindAnchoredSections(line: PuzzleLine)
    modifies 
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n]
    {
        var i: int;
        var fillRange: array?<int>;
        var firstSection: Section, lastSection: Section;

        if (line.Sections.Length > 0)
        {
            firstSection := line.Sections[0];
            lastSection  := line.Sections[line.Sections.Length - 1];

            // find sections anchored to start of line
            fillRange := null;
            for i := 0 to |line.Cells| 
            {
                if line.Cells[i].AISolution == CellValue.NULL
                {
                    break;
                }
                else if line.Cells[i].AISolution == CellValue.1
                {
                    fillRange := new int[] [i, i + firstSection.Length - 1];
                    break;
                }
            }

            if fillRange != null
            {
                for i := fillRange[0] to fillRange[1] + 1
                {
                    if (i < |line.Cells|) 
                    // original code has simply line.cells[i] as the condition; 
                    // think it's leveraging JavaScripts reading-out-of-bounds behaviour
                    {
                        this.SetCellSolution(line.Cells[i],CellValue.1);
                    }
                }
                if (i < |line.Cells|)
                {
                    this.SetCellSolution(line.Cells[i],CellValue.0);
                }
            }

            // find sections anchored to end of line
            fillRange := null;

            for i := |line.Cells| downto 0
            {
                if line.Cells[i].AISolution == CellValue.NULL
                {
                    break;
                }
                else if line.Cells[i].AISolution == CellValue.1
                {
                    fillRange := new int[] [i - lastSection.Length + 1, i];
                    break;
                }
            }
            if fillRange != null
            {
                for i := fillRange[0] to fillRange[1] + 1
                {
                    if (i < |line.Cells|)
                    {
                        this.SetCellSolution(line.Cells[i],CellValue.1);
                    }
                }
                if (fillRange[0] - 1 < |line.Cells|)
                {
                    this.SetCellSolution(line.Cells[fillRange[0] - 1],CellValue.0);
                }
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