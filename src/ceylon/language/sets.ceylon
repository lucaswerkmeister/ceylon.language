"Returns an iterator that yields [[zero]] and then alternatingly the values from [[it]] and their [[negation|Number.negated]]."
Iterator<Num> mirror<Num>(Num zero, Iterator<Num> it)
        given Num satisfies Number<Num>
        ⇒ object satisfies Iterator<Num> {
    value absIt = { ∀ (seq in { [zero], *(object satisfies Iterable<Num> { iterator() => it; }).map((e) ⇒ [e,e])}) ∀ (e in seq) e }.iterator();
    variable Boolean negate = true;
    shared actual Num next() {
        assert (is Num abs = absIt.next());
        value ret = negate then abs.negated else abs;
        negate = negate then false else true;
        return ret;
    }
};

"The [Stern–Brocot sequence][w:stern-brocot],
 which yields every positive rational number exactly once (in its most reduced form).
 Calculated in the form presented by
 Parker, Matt (2014), [“Infinite Fractions”][y:inffrac], [Numberphile][y:numberphile]:
 
 - begin with 1, 1
 - repeatedly:
     - form the sum of the next two values
     - append that sum to the sequence
     - append the second of the two values to the sequence
 
 Resulting in the sequence:
 
 > 1, 1, 2, 1, 3, 2, 3, 1, 4, …
 
 Dividing subsequent elements of the sequence then yields positive rational numbers:
 
 > 1⁄1, 1⁄2, 2⁄1, 1⁄3, 3⁄2, 2⁄3, 3⁄1, 1⁄4, …
 
 We build up the sequence during iteration,
 immediately discarding values from the front that we no longer need.
 
 [w:stern-brocot]: https://en.wikipedia.org/wiki/Stern–Brocot_tree
 [y:inffrac]: https://www.youtube.com/watch?v=DpwUVExX27E
 [y:numberphile]: https://www.youtube.com/user/numberphile"
Iterator<Float> sternBrocot ⇒ object satisfies Iterator<Float> {
            
    variable Integer[] sequence = [1, 1];
    
    shared actual Float next() {
        assert (∃ i1 = sequence[0], ∃ i2 = sequence[1]);
        sequence = sequence.append([i1+i2, i2]).rest;
        return i1.float ⁄ i2.float;
    }
};

"The set of natural numbers (starting with 1)."
shared Set<Integer> ℕ = object satisfies Set<Integer> ∩ Identifiable {
    
    shared actual Iterator<Integer> iterator() ⇒ (1…runtime.maxIntegerValue).iterator();
    shared actual Integer size ⇒ runtime.maxIntegerValue;
    shared actual Set<Integer> clone() ⇒ this; // immutable
    
    shared actual Boolean contains(Object element) ⇒ if (is Integer element) then element > 0 else false;
    
    // KISS. Don’t judge me.
    shared actual Set<Integer∪Other> union<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.union(this);
    shared actual Set<Integer∩Other> intersection<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.intersection(this);
    shared actual Set<Integer∪Other> exclusiveUnion<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.exclusiveUnion(this);
    
    // non-trivial to implement, don’t bloat the language module
    shared actual Set<Integer> complement<Other>(Set<Other> set)
            given Other satisfies Object {
        if (set == this) {
            return emptySet;
        } else {
            throw Exception("Illegal operation");
        }
    }
    
    shared actual Integer hash ⇒ "ℕ".hash;
    shared actual Boolean equals(Object that)
            ⇒ if (is Identifiable that) then this === that else false; // way too expensive to check any other equality
};

"The set of natural numbers, including 0."
shared Set<Integer> ℕ₀ = object satisfies Set<Integer> ∩ Identifiable {
    
    shared actual Iterator<Integer> iterator() ⇒ (0…runtime.maxIntegerValue).iterator();
    // shared actual Integer size ⇒ runtime.maxIntegerValue + 1; // doesn’t work :)
    shared actual Set<Integer> clone() ⇒ this; // immutable
    
    shared actual Boolean contains(Object element) ⇒ if (is Integer element) then element ≥ 0 else false;
    
    // KISS. Don’t judge me.
    shared actual Set<Integer∪Other> union<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.union(this);
    shared actual Set<Integer∩Other> intersection<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.intersection(this);
    shared actual Set<Integer∪Other> exclusiveUnion<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.exclusiveUnion(this);
    
    // non-trivial to implement, don’t bloat the language module
    shared actual Set<Integer> complement<Other>(Set<Other> set)
            given Other satisfies Object {
        if (set == this) {
            return emptySet;
        } else {
            throw Exception("Illegal operation");
        }
    }
    
    shared actual Integer hash ⇒ "ℕ₀".hash;
    shared actual Boolean equals(Object that)
            ⇒ if (is Identifiable that) then this === that else false; // way too expensive to check any other equality
};

"The set of integer numbers."
shared Set<Integer> ℤ = object satisfies Set<Integer> ∩ Identifiable {
    
    shared actual Iterator<Integer> iterator() ⇒ mirror(0, (1…runtime.maxIntegerValue).iterator());
    // shared actual Integer size ⇒ 2 * runtime.maxIntegerValue + 1; // doesn’t work :)
    shared actual Set<Integer> clone() ⇒ this; // immutable
    
    shared actual Boolean contains(Object element) ⇒ element is Integer;
    
    // KISS. Don’t judge me.
    shared actual Set<Integer∪Other> union<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.union(this);
    shared actual Set<Integer∩Other> intersection<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.intersection(this);
    shared actual Set<Integer∪Other> exclusiveUnion<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.exclusiveUnion(this);
    
    // non-trivial to implement, don’t bloat the language module
    shared actual Set<Integer> complement<Other>(Set<Other> set)
            given Other satisfies Object {
        if (set == this) {
            return emptySet;
        } else {
            throw Exception("Illegal operation");
        }
    }
    
    shared actual Integer hash ⇒ "ℤ".hash;
    shared actual Boolean equals(Object that)
            ⇒ if (is Identifiable that) then this === that else false; // way too expensive to check any other equality
};

"The set of rational numbers.
 
 (All [[Floats]] except infinities and NaN are rational numbers, namely binary fractions.)"
shared Set<Integer∪Float> ℚ = object satisfies Set<Float∪Integer> ∩ Identifiable {
    
    shared actual Iterator<Float> iterator() ⇒ mirror(0.0, sternBrocot);
    shared actual Set<Integer∪Float> clone() ⇒ this; // immutable
    
    shared actual Boolean contains(Object element)
            ⇒ switch (element)
              case (is Integer) true
              case (is Float) element.finite
              else false;
    
    // KISS. Don’t judge me.
    shared actual Set<Integer∪Float∪Other> union<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.union(this);
    shared actual Set<<Integer∪Float>∩Other> intersection<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.intersection(this);
    shared actual Set<Integer∪Float∪Other> exclusiveUnion<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.exclusiveUnion(this);
    
    // non-trivial to implement, don’t bloat the language module
    shared actual Set<Integer> complement<Other>(Set<Other> set)
            given Other satisfies Object {
        if (set == this) {
            return emptySet;
        } else {
            throw Exception("Illegal operation");
        }
    }
    
    shared actual Integer hash ⇒ "ℚ".hash;
    shared actual Boolean equals(Object that)
            ⇒ if (is Identifiable that) then this === that else false; // way too expensive to check any other equality
};

"The set of real numbers.
 
 (Because of the way [[Float]]s are represented, this is for all intents and purposes identical to [[ℚ]].)"
shared Set<Integer∪Float> ℝ = object satisfies Set<Float∪Integer> ∩ Identifiable {
    
    shared actual Iterator<Float> iterator() ⇒ mirror(0.0, sternBrocot);
    shared actual Set<Integer∪Float> clone() ⇒ this; // immutable
    
    shared actual Boolean contains(Object element)
            ⇒ switch (element)
              case (is Integer) true
              case (is Float) element.finite
              else false;
    
    // KISS. Don’t judge me.
    shared actual Set<Integer∪Float∪Other> union<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.union(this);
    shared actual Set<<Integer∪Float>∩Other> intersection<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.intersection(this);
    shared actual Set<Integer∪Float∪Other> exclusiveUnion<Other>(Set<Other> set)
            given Other satisfies Object ⇒ set.exclusiveUnion(this);
    
    // non-trivial to implement, don’t bloat the language module
    shared actual Set<Integer> complement<Other>(Set<Other> set)
            given Other satisfies Object {
        if (set == this) {
            return emptySet;
        } else {
            throw Exception("Illegal operation");
        }
    }
    
    shared actual Integer hash ⇒ "ℝ".hash;
    shared actual Boolean equals(Object that)
            ⇒ if (is Identifiable that) then this === that else false; // way too expensive to check any other equality
};
