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

class Solver
{
    var Lines: array<Line>
    
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
}

