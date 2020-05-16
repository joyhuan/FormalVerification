(** **** Exercise: 5 stars, standard (linsearch_correct)  *)

(** Prove that [linsearch] is correct. The simpler your
    implementations of [linsearch] and [get], the better.

    Hints: Start by inducting on the input list. The proof is somewhat
    long and requires a lot of [destruct] and [bdestruct] but only the
    one use of [induction]. We leave it to you to discover and factor
    out any helper lemmas you might like. You do not need to write any
    fancy Ltac automation. *)

Theorem linsearch_correct : correct_search linsearch.

(** We repeat the definition of [sorted] from _Software Foundations_:
    *)

Inductive sorted: list nat -> Prop :=
| sorted_nil:
    sorted nil
| sorted_1 : forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

(** Now we specify what it means to be a correct search function. This
    definition is a formal rendition of the informal specification of
    the correctness of [linsearch] as given above. *)

Definition correct_search f :=
  forall (a : list nat) (v : nat) (k : nat),
    sorted a
    -> f a v = k
    -> (forall i, 1 <= i <= k ->
            forall u, get a i = Some u -> u <= v)
    /\ (forall i, k < i <= length a ->
            forall u, get a i = Some u -> u > v).

Lemma bounds_helper : forall i j,
    1 <= S i <= S j -> i > 0 -> 1 <= i <= j.

Lemma linsearch_helper : forall h t v k,
    v < h
    -> sorted (h :: t)
    -> linsearch (h :: t) v = k
    -> k = 0 /\ linsearch t v = 0.

Lemma sorted_helper : forall h t,
    sorted (h :: t) -> sorted t.