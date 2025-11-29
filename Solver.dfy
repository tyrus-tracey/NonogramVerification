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

    method FindKnownPositivesAndNegatives(line: PuzzleLine)
    requires line in Lines[..]
    requires line.Length > 0
    /*
    ensures this.Lines == old(this.Lines)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>  
        this.Lines[j].Cells == old(this.Lines[j].Cells)
    */
    modifies 
        line,
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n]
    {
        var totalCellCounts: array<int> := new int[line.Length]((_) => 0);
        var section: Section;
        var cellCounts: array<int>;
        var possibleStartIndex: int, start: int, end: int;
        var cellCount: int, cell: PuzzleCell;
        for sectionKey: int := 0 to line.Sections.Length
        invariant 0 <= sectionKey < line.Sections.Length
        {
            section := line.Sections[sectionKey];
            cellCounts := new int[line.Length]((_) => 0);
            // keep two counts: 1) all common cells for this section, and 2) cells where no section can be
            for startIndexKey: int := 0 to section.PossibleStartIndexes.Length
            invariant 0 <= startIndexKey < section.PossibleStartIndexes.Length
            {
                possibleStartIndex := section.PossibleStartIndexes[startIndexKey];
                start := possibleStartIndex;
                end := start + section.Length - 1;

                for i: int := start to end + 1
                {
                    cellCounts[i] := cellCounts[i] + 1;
                    totalCellCounts[i] := totalCellCounts[i] + 1;
                }
            }
            // common to all possibilities, solve as positive
            for cellCountKey: int := 0 to cellCounts.Length
            invariant 0 <= cellCountKey < cellCounts.Length
            {
                if (0 <= cellCountKey < |line.Cells|)
                {
                    cellCount := cellCounts[cellCountKey];
                    cell := line.Cells[cellCountKey];
                    if (cell.AISolution == NULL && cellCount == section.PossibleStartIndexes.Length)
                    {
                        SetCellSolution(cell, CellValue.1);
                    }
                }
            }
            // no possible cells, remove as a possibility
            for cellCountKey: int := 0 to cellCounts.Length
            invariant 0 <= cellCountKey < cellCounts.Length
            {
                if (0 <= cellCountKey < |line.Cells|)
                {
                    cellCount := totalCellCounts[cellCountKey];
                    cell := line.Cells[cellCountKey];
                    if (cell.AISolution == NULL && cellCount == 0)
                    {
                        SetCellSolution(cell, CellValue.0);
                    }
                }
            }
        }
        
    }

    method FindAnchoredSections(line: PuzzleLine)
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
        var i: int;
        var fillRange: array?<int>;
        var firstSection: Section, lastSection: Section;

        if (line.Sections.Length > 0)
        {
            firstSection := line.Sections[0];
            lastSection  := line.Sections[line.Sections.Length - 1];

            // find sections anchored to start of line
            fillRange := null;
            for j: int := 0 to |line.Cells| 
            invariant 0 <= j <= |line.Cells|
            invariant forall j: int :: 0 <= j < this.Lines.Length ==>
                this.Lines[j].Cells == old(this.Lines[j].Cells) &&
                this.Lines[j].Sections == old(this.Lines[j].Sections)
            {
                if line.Cells[j].AISolution == CellValue.NULL
                {
                    break;
                }
                else if line.Cells[j].AISolution == CellValue.1
                {
                    fillRange := new int[] [j, j + firstSection.Length - 1];
                    break;
                }
            }

            if fillRange != null
            {
                i := fillRange[0];
                //for i := fillRange[0] to fillRange[1] + 1
                // doing a while loop for now because not sure how to tell Dafny fr0<=fr1
                // TODO fix that (should be possible)
                while i <= fillRange[1]
                //invariant fillRange[0] <= i <= fillRange[1] + 1
                invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                    this.Lines[i].Cells == old(this.Lines[i].Cells) &&
                    this.Lines[i].Sections == old(this.Lines[i].Sections)
                {
                    if (0 <= i < |line.Cells|) 
                    // original code has simply line.cells[i] as the condition; 
                    // think it's leveraging JavaScript's reading-out-of-bounds behaviour
                    {
                        this.SetCellSolution(line.Cells[i],CellValue.1);
                    }
                    i := i+1;
                }
                if (0 <= i < |line.Cells|)
                {
                    this.SetCellSolution(line.Cells[i],CellValue.0);
                }
            }

            // find sections anchored to end of line
            fillRange := null;

            for i := |line.Cells| downto 0
            invariant fillRange != null ==> fillRange.Length == 2
            invariant fillRange != null ==> 0 < fillRange[0] <= fillRange[1]
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
                var k: int := fillRange[0];
                // TODO as for loop if possible
                //for i := fillRange[0] to fillRange[1] + 1
                while k <= fillRange[1]
                //invariant fillRange[0] <= i <= fillRange[1] + 1
                invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                    this.Lines[i].Cells == old(this.Lines[i].Cells) &&
                    this.Lines[i].Sections == old(this.Lines[i].Sections)
                {
                    if (0 <= k < |line.Cells|)
                    {
                        SetCellSolution(line.Cells[k],CellValue.1);
                    }
                    k := k+1;
                }
                if (0 <= fillRange[0] - 1 < |line.Cells|)
                {
                    SetCellSolution(line.Cells[fillRange[0] - 1],CellValue.0);
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