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

    method Solve()
    requires forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
    ensures forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid() &&
        this.Lines[i].Cells == old(this.Lines[i].Cells)
    modifies 
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < this.Lines[m].Sections.Length &&
            c == this.Lines[m].Sections[n]
    {
        //NOTE: Original code has a bunch of stuff for UI/logging solutions/resetting puzzles that aren't relevant to verification, and are omitted.

        var totalSolved: int := this.GetTotalSolved();
        while(totalSolved < this.Puzzle.Cells.Length)
        decreases this.Puzzle.Cells.Length - totalSolved
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
            this.Lines[i].Valid() &&
            this.Lines[i].Cells == old(this.Lines[i].Cells) &&
            this.Lines[i].Sections == old(this.Lines[i].Sections)
        {
            for lineKey: int := 0 to this.Lines.Length
            invariant 0 <= lineKey <= this.Lines.Length
            invariant forall i: int :: 0 <= i < this.Lines.Length ==> 
                this.Lines[i].Valid() &&
                this.Lines[i].Cells == old(this.Lines[i].Cells) &&
                this.Lines[i].Sections == old(this.Lines[i].Sections)
            {
                var line: PuzzleLine := this.Lines[lineKey];
                if (!line.Solved)
                {
                    this.EliminateImpossibleFits(line);
                }
                if (!line.Solved)
                {
                    this.FindKnownPositivesAndNegatives(line);
                }
                if (!line.Solved)
                {
                    //TODO:
                    //this.FindSectionDefiningChains(line);
                }
                if (!line.Solved)
                {
                    this.FindAnchoredSections(line);
                }
                if (!line.Solved)
                {
                    this.FindCompletedSections(line);
                }
                if (!line.Solved)
                {
                    this.FindCompletedLines(line);
                }
            }
            totalSolved := this.GetTotalSolved();
        }
        
    }

    method EliminateImpossibleFits(line: PuzzleLine)
    requires line in Lines[..]
    requires forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
    // ensures forall i: int :: 0 <= i < this.Lines.Length ==>
    //     this.Lines[i].Valid()
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
        var minimumStartIndex: int := 0;
        var maximumStartIndex: int := 0;

        if (line.Sections.Length == 0) {

            for lineCellKey: int := 0 to line.Length 
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
            invariant 0 <= lineCellKey <= |line.Cells|
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                    this.Lines[i].Cells == old(this.Lines[i].Cells)
            {
                this.SetCellSolution(line.Cells[lineCellKey], CellValue.0);
            }
        }

        //tighten range if negative cells start the line
        for lineKey: int := 0 to line.Length
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
        invariant 0 <= lineKey <= |line.Cells| 
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                    this.Lines[i].Cells == old(this.Lines[i].Cells)
        {
            if (line.Cells[lineKey].AISolution == CellValue.0) {
                minimumStartIndex := minimumStartIndex + 1;
            } else {
                break;
            }
        }

        //tighten range if negative cells end the line
        for lineKey: int := |line.Cells| downto 0
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
        invariant 0 <= lineKey <= |line.Cells|
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                    this.Lines[i].Cells == old(this.Lines[i].Cells)
        {
            if (line.Cells[lineKey].AISolution == CellValue.0) {
                minimumStartIndex := minimumStartIndex - 1;
            } else {
                break;
            }
        }

        for lineSectionKey: int := 0 to line.Sections.Length
        invariant 0 <= lineSectionKey <= line.Sections.Length
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
        {
            var section: Section := line.Sections[lineSectionKey];
            var newPossibleStartIndexes: array<nat>;

            for startIndexKey: int := 0 to section.PossibleStartIndexes.Length
            invariant 0 <= startIndexKey <= section.PossibleStartIndexes.Length
            //must keep possibleStartIndex + section length in bounds
            {
                var possibleStartIndex := section.PossibleStartIndexes[startIndexKey];
                var testCell := line.Cells[possibleStartIndex + section.Length];

                if(possibleStartIndex < minimumStartIndex || possibleStartIndex > maximumStartIndex) {
                    //newPossibleStartIndexes := remove from array
                }

                if(exists testCell: PuzzleCell :: testCell.AISolution == CellValue.1) {
                    // newPossibleStartIndexes := remove from array
                }
            }
        }
    }


    method FindKnownPositivesAndNegatives(line: PuzzleLine)
    requires line in this.Lines[..]
    requires forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
    ensures this.Lines == old(this.Lines)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>  
        this.Lines[j].Cells == old(this.Lines[j].Cells)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>
        this.Lines[j].Sections == old(this.Lines[j].Sections)
    ensures forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
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
        var cellCounts: array<int> := new int[line.Length]((_) => 0);
        var possibleStartIndex: int, start: int, end: int;
        var cellCount: int, cell: PuzzleCell;
        for sectionKey: int := 0 to line.Sections.Length
        invariant 0 <= sectionKey <= line.Sections.Length
        invariant forall j: int :: 0 <= j < this.Lines.Length ==>
            this.Lines[j].Cells == old(this.Lines[j].Cells) &&
            this.Lines[j].Sections == old(this.Lines[j].Sections) &&
            this.Lines[j].Length == old(this.Lines[j].Length)
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
            this.Lines[i].Valid()
        invariant cellCounts.Length == totalCellCounts.Length
        {
            section := line.Sections[sectionKey];
            cellCounts := new int[line.Length]((_) => 0);
            // keep two counts: 1) all common cells for this section, and 2) cells where no section can be
            for startIndexKey: int := 0 to section.PossibleStartIndexes.Length
            invariant 0 <= startIndexKey <= section.PossibleStartIndexes.Length
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
            invariant cellCounts.Length == totalCellCounts.Length
            invariant forall j: int :: 0 <= j < this.Lines.Length ==>
                this.Lines[j].Cells == old(this.Lines[j].Cells) &&
                this.Lines[j].Sections == old(this.Lines[j].Sections) &&
                this.Lines[j].Length == old(this.Lines[j].Length)
            {
                possibleStartIndex := section.PossibleStartIndexes[startIndexKey];
                start := possibleStartIndex;
                end := start + section.Length - 1;

                for i: int := start to end + 1
                invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                    this.Lines[i].Valid()
                invariant forall j: int :: 0 <= j < this.Lines.Length ==>
                    this.Lines[j].Cells == old(this.Lines[j].Cells) &&
                    this.Lines[j].Sections == old(this.Lines[j].Sections) &&
                    this.Lines[j].Length == old(this.Lines[j].Length)
                {
                    cellCounts[i] := cellCounts[i] + 1;
                    totalCellCounts[i] := totalCellCounts[i] + 1;
                }
            }
            // common to all possibilities, solve as positive
            for cellCountKey: int := 0 to cellCounts.Length
            invariant 0 <= cellCountKey <= cellCounts.Length
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
            invariant forall j: int :: 0 <= j < this.Lines.Length ==>
                this.Lines[j].Cells == old(this.Lines[j].Cells) &&
                this.Lines[j].Sections == old(this.Lines[j].Sections) &&
                this.Lines[j].Length == old(this.Lines[j].Length)
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
            invariant 0 <= cellCountKey <= cellCounts.Length
            invariant cellCounts.Length == totalCellCounts.Length
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
            invariant forall j: int :: 0 <= j < this.Lines.Length ==>
                this.Lines[j].Cells == old(this.Lines[j].Cells) &&
                this.Lines[j].Sections == old(this.Lines[j].Sections) &&
                this.Lines[j].Length == old(this.Lines[j].Length)
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
    requires forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
    ensures this.Lines == old(this.Lines)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>  
        this.Lines[j].Cells == old(this.Lines[j].Cells) &&
        this.Lines[j].Sections == old(this.Lines[j].Sections)
    ensures forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
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
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
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
                    this.Lines[i].Valid()
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
            invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Valid()
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
                    this.Lines[i].Valid()
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
    requires forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
    ensures line.Sections == old(line.Sections)
    ensures this.Lines == old(this.Lines)
    ensures forall i:int :: 0 <= i < this.Lines.Length ==>  
        this.Lines[i].Cells == old(this.Lines[i].Cells) &&
        this.Lines[i].Sections == old(this.Lines[i].Sections) &&
        this.Lines[i].Valid()
    modifies 
        line,
        this.Lines[..],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < |this.Lines[m].Cells| &&
            c == this.Lines[m].Cells[n],
        set c | exists m,n ::
            0 <= m < this.Lines.Length &&
            0 <= n < this.Lines[m].Sections.Length &&
            c == this.Lines[m].Sections[n]
    {
        for sectionKey: int := 0 to line.Sections.Length
        invariant 0 <= sectionKey <= line.Sections.Length
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
                this.Lines[i].Cells == old(this.Lines[i].Cells) &&
                this.Lines[i].Sections == old(this.Lines[i].Sections) &&
                this.Lines[i].Valid()
        {
            var section := line.Sections[sectionKey];

            if (!section.Solved && section.PossibleStartIndexes.Length == 1)
            {
                var firstNegative: int := section.PossibleStartIndexes[0];
                firstNegative := firstNegative - 1;
                var lastNegative := section.PossibleStartIndexes[0] + section.Length;

                if (0 <= firstNegative < |line.Cells| && line.Cells[firstNegative].AISolution == CellValue.NULL)
                {
                    SetCellSolution(line.Cells[firstNegative], CellValue.0);
                }
                if (0 <= lastNegative < |line.Cells| && line.Cells[lastNegative].AISolution == CellValue.NULL)
                {
                    SetCellSolution(line.Cells[lastNegative], CellValue.0);
                }
                section.Solved := true;
            }
        }
    }

    method FindCompletedLines(line: PuzzleLine)
    requires line in Lines[..]
    requires forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
    ensures this.Lines == old(this.Lines)
    ensures forall i:int :: 0 <= i < this.Lines.Length ==>  
        this.Lines[i].Cells == old(this.Lines[i].Cells) &&
        this.Lines[i].Sections == old(this.Lines[i].Sections)
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
                this.Lines[i].Cells == old(this.Lines[i].Cells) &&
                this.Lines[i].Sections == old(this.Lines[i].Sections) &&
                this.Lines[i].Valid()
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
    requires forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
    ensures this.Lines == old(this.Lines)
    ensures forall j:int :: 0 <= j < this.Lines.Length ==>  
        this.Lines[j].Cells == old(this.Lines[j].Cells) &&
        this.Lines[j].Sections == old(this.Lines[j].Sections)
    ensures forall i: int :: 0 <= i < this.Lines.Length ==>
        this.Lines[i].Valid()
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
        invariant forall i: int :: 0 <= i < this.Lines.Length ==>
            this.Lines[i].Valid()
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