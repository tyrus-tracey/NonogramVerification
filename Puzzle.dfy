include "PuzzleCell.dfy"

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