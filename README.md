# Formal Verification

CS 4160 Formal Verification and CS 5414 Distributed Computing Principles are my favorite CS 
courses at Cornell. (If you care to know, MATH 2230 Honor Linear Algebra and MATH 3320 Number Theory
are my favorite math courses)

From the course website, its description goes like this
> Catalog Description: An introduction to formal verification, focusing on correctness of functional 
and imperative programs relative to mathematical specifications. Topics include computer-assisted 
theorem proving, logic, programming language semantics, and verification of algorithms and data 
structures. 

I'm always frustrated when explaining to people why I love it so much. This is because at the 
first sight, you may think this is no-brainer. To give you an example, in this class we try to prove 
that for a number n, if it is even then there exists a k, such as n = 2k; if odd, exists a k such 
that n = 2k + 1. 
```
(** **** Exercise: 3 stars, standard (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
```
In the first sight, it sounds like an elementary school math problem. However, it is really not so. 
The proof reintroduces how numbers, operations, and logic are defined. We take even/odd for granted and +,-,*,/ are so straightforward that we have already formed a mental shortcut. This is fine 
for tasks as easy as number operations. But when the difficulty level increases, it will become much
less intuitive. In fact, believe it or not, the difficulty level doesn't even need to be tuned
much that you will feel so lost. To help you get a better sense, this is the only problem that I 
skipped in the final exam. 
```
(** **** Exercise: 5 stars, standard (linsearch_correct)  *)

(** Prove that [linsearch] is correct. The simpler your
    implementations of [linsearch] and [get], the better.

    Hints: Start by inducting on the input list. The proof is somewhat
    long and requires a lot of [destruct] and [bdestruct] but only the
    one use of [induction]. We leave it to you to discover and factor
    out any helper lemmas you might like. You do not need to write any
    fancy Ltac automation. *)

Theorem linsearch_correct : correct_search linsearch.
```
Basically we are trying to prove that linear search is a valid sorting algorithm. Now, does that 
sound easy task for you? It might naturally follows that we at least need to first define linsearch 
and correct_search. And then we will piece the two definitions to form a proof. Just give you a 
flavor I attached the needed definitions and lemmas before we get to the proof. You will need to design more by yourself to get the proof done. 

```
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
```

Tbh I worked over this problems for more than three hours. At a few points I was very close to finish
the proof but still fail at the margin. But I can tell you every second of the stuggle and the toil is 
totally worth it. I became more aware of subconscious, became more alert at detecting false plausible assumptions, and became more adept at coining counterexamples. Logic unknots from chaos and started to form clear concrete maps in my mind.

Though many people took this class because they are passionate and ambitious to use computer to 
do proofs both in math theories and the correctness of their program (the latter case is actually
much harder than most people imagine), I took this class because I wanted to improve my logic. Though
I cannot say I am good at logic after taking the class, I am definitely way better. 

I still haven't figured out a way to explain Formal Verification to people so that it gets the 
respect that it deserves, but I will continue working on it. Hope I can make you appreciate its power as much as I do. 
