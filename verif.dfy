datatype SolutionStatus = NULL | 0 | 1

class PuzzleCell
{
    var Index: int
    var Column: int
    var Row: int
    var Solution: SolutionStatus
    var UserSolution: SolutionStatus
    var AISolution: SolutionStatus
}

class Line 
{
    var Type: string
    var Index: int
    var Length: int
    var MinimumSectionLength: int
    var Sections: array<array<int>>
    var Cells: array<PuzzleCell>
    var Solved: bool
}

class Puzzle
{
    var Width: int
    var Height: int
    var TotalCells: int
    var Cells: array<PuzzleCell>
    var RowHints: array<int>
    var ColumnHints: array<int>
    // there's a "creator or null" property here but 
    // I get the feeling it's for UI so just a comment for now
    var Grid: array2<int> // solution grid used in construction

    constructor(width: int, height: int)
    requires width >= 0 && height >= 0 && (width > 1 || height > 1)
    {
        // original function has handling for non-number inputs, which I don't think we need
        Width := width;
        Height := height;
        TotalCells := width * height;
        /*
        new;
        Reset();
        */

        Cells := new PuzzleCell[0];
        RowHints := new int[0];
        ColumnHints := new int[0];
        Grid := new int[height, width]((_,_) => 0);
    }

    /*
    // this is used in a few places, including the constructor, but Dafny constructors don't like init via fn call
    // so I'm just adding a comment for now and maybe we'll need it later
    method Reset()
    modifies Cells, RowHints, ColumnHints
    {
        Cells := new PuzzleCell[0];
        RowHints := new int[0];
        ColumnHints := new int[0];
        Grid := new int[height, width]((_,_) => 0);
    }
    */
}

class Solver
{
    var Lines: array<Line>
    var Puzzle: Puzzle

    constructor(puzzle: Puzzle)
    {
        Puzzle := puzzle;
    }
    
    method SetCellSolution(puzzleCell: PuzzleCell, value: SolutionStatus)
    modifies this.Lines[..]
    {
        var lineKey: int, cellKey: int, cellsSolved: int;
        var line: Line;
        var isRow:bool , isCol: bool;
        var cell: PuzzleCell;

        if puzzleCell.AISolution != NULL
        {
            return;
        }

        for lineKey := 0 to Lines.Length
        {
            line := Lines[lineKey];
            isRow := line.Type == "row" && line.Index == puzzleCell.Row;
            isCol := line.Type == "column" && line.Index == puzzleCell.Column;
            cellsSolved := 0;

            if (isRow || isCol)
            {
                for cellKey := 0 to line.Cells.Length
                {
                    cell := line.Cells[cellKey];

                    if (cell.Index == puzzleCell.Index) {
                        cell.AISolution := value;
                    } else if (cell.AISolution == NULL) {
                        cellsSolved := cellsSolved + 1;
                    }
                }

                if (cellsSolved == line.Length) {
                    line.Solved := true;
                }
            }
        }
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
}

