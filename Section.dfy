class Section
{
    var Index: int
    var Length: int
    var PossibleStartIndexes: array<int>
    var KnownIndexes: array<int>
    var Solved: bool

    constructor(index: int, length: int, possibleStartIndexes: array<int>, knownIndexes: array<int>)
    {
        Index := index;
        Length := length;
        PossibleStartIndexes := possibleStartIndexes;
        KnownIndexes := knownIndexes;
        Solved := false;
    }
}