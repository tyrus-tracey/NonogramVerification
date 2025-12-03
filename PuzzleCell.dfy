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
    requires solution != CellValue.NULL
    modifies this`AISolution
    ensures AISolution != CellValue.NULL
    ensures old(AISolution) != CellValue.NULL ==> AISolution != CellValue.NULL
    {
        AISolution := solution;
    }

    constructor ()
    ensures Index == 0 && Column == 0 && Row == 0 &&
        Solution == CellValue.NULL && UserSolution == CellValue.NULL && AISolution == CellValue.NULL
    {
        Index := 0;
        Column := 0;
        Row := 0;
        Solution := NULL;
        UserSolution := NULL;
        AISolution := NULL;
    }
}
