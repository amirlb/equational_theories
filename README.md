## Lists on unknown implications

These files exist in this directory:

* `all_unknown.txt` - all the implications that are as yet undecided

* `components.txt` - known equivalence classes of implications, one per line

* `modulo_equivalence.txt` - only a single unknown implication per pair of equivalence classes

* `only_strongest.txt` - subset of `modulo_equivalence.txt`. if we know `A => B` and `C => D`,
    and the status of all of `A => C`, `B => C`, `A => D`, `B => D` is unknown, this file will
    include only `B => C` out of the four.
