datatype CellValue = NULL | 0 | 1

class PuzzleCell
{
    var Index: nat
    var Column: nat
    var Row: nat
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