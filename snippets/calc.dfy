lemma LeftIdentity<A,B>(x: A, f: A → M<B>) {
  calc {
       Bind(Return(x), f);
    == Join(Map(Cons(x, Nil), f));
    == Join(Cons(f(x), Nil));
    == Concat(f(x), Nil);
    == { assert ∀ xs : M<B> :: Concat(xs, Nil) == xs; } f(x);
  }
}
