## Notes - 5 October 2015 - 3:33 PM

Starting on the partial order specification.  This should be pretty simple using Coq's built-in partial order definition.

## Notes - 31 August 2015 - 9:47 AM

Catching up with the semantics document first this morning.  Need to take care of:

* [x] add `att-start`
* [x] add rooted to well-formedness of `M+`
* [x] remove `btm` and `rtm` replacing with `ms`
* [ ] add definition of `touch`
* [ ] add definition of execution defined as poset over `E`
* [ ] add definition of specification as an execution with no adversary events
* [ ] add definition of admits
* [ ] add definition of adversary events

This will get the specification up through Lemma 1.  At that point, let's try to mechanize the proof of Lemma 1.

10:47 AM Crap.  Dropbox and git do not work at all well together.  Dropbox just jacked my theory by merging the development repo with the master repo.  Need to figure this out, but for now I'll just work in the master repo.

Still finding the irreflexive theorem for transitive closure.  I may need to find a new way to specify the M and M+ relations.  I got rid of the transitive closure definition from the Coq libraries, but that go me nowhere.  I need something to cause the contradiction I need when `M+(o,o)` holds.

10:54 AM Fixed the problems created by git and Dropbox.  Still need a resolution for getting them to work together, but that is not for now.

10:54 AM Added `att_start` and removed `btm`. 

## Notes - 26 August 2015 - 11:18 AM

Found a small problem in `is_well_formed_M` that does not impact soundness.  Nice to get rid of though as it simplifies the proof.

2:12 PM - Fixed the previous problem.  Working on how to get a contradiction out of the well-formedness condition and how to specify the partial order.

3:08 PM - Need to prove `forall o, ~m+(o,o)`.  When you unfold `not` the goal it becomes:

	m+(o,o) -> False

and `m+(o,o)` becomes dan assumption from which `False` must be derived.  Basically, introducing `m+(o,o)` must cause some kind of inconsistency from which `False` is an immediate consequence.

The current example `m+` is irreflexive.  But assuming that it is reflexive does not cause a contradiction.  Said differently, adding `m+(o,o)` does not conflict with anything the relation specifies.  There are a number of options:

1. Find an antecedent or assumption to create a contradiction
2. Find a direct proof that does not rely on deriving `False`.

The current state following induction on `o` is:

	4 subgoals, subgoal 1 (ID 507)
	  
	  H : clos_trans Obj m RTM RTM
	  ============================
	   False
	
	subgoal 2 (ID 508) is:
	 False
	subgoal 3 (ID 509) is:
	 False
	subgoal 4 (ID 510) is:
	 False

Exactly as expected.  There are 4 objects including the RTM and one subgoal for each.  The first subgoal is discharged by knowing that `RTM` is not measured by anything.  Thus, having `m RTM RTM` in the transitive closure causes a contradiction.  As does having `m+ y RTM` from the second case.  What should the contradiction be for the other cases?  That's what's perplexing right now.

## Notes - 25 August 2015 - 11:38 PM

Cleaned up several proofs to make them more automated and abstract.  Not much more than that today.  Still getting rolling on the partial order specification.

Use `generalize` to introduce new lemmas to the assumption set.  What this does is adds the lemma as a condition on the proof goal.  You can them use `intros` to move it into the antecedent.  Pretty cool, but I hadn't figured that out yet.

## Notes - 21 August 2015 - 8:40 AM

What's going on with the proofs of asymmetric and irreflexivity is  we don't have a law of the excluded middle.  Specifically:

```
~A\/A
```

Need to find a way to prove this directly by possibly taking the inverse of the relation.

`~R(o,o)` 

## Notes - 20 August 2015 - 10:16 AM

Diving back in to the partial order specification and thinking about the definition of `admit`.

The form of the `exist` constructor for `sig` is:

```
exist property value proof
```

where `proof` is the proof that `property` holds over `value`.  Don't forget this.  In a `match` only two arguments are required.

5:26 PM - Definitions of well-formedness are complete using subset types to define types that include only well-formed M and M+.  This seems to work quite well if I can get the proofs to pop out.

The difficulty seems to be finding a contradiction that results from `clos_trans m o o` holding true.  This would allow me to discharge the false conclusion and complete the proof.  With other relation definitions, the problem was that relations over numbers *with established properties* would introduce things inconsistent with those properties.  This made the proofs quite simple.  The elements of `Obj` don't have enough properties.  However, I know what I'm looking for.

## Notes - 19 August 2015 - 12:26 PM

Started defining a partial ordering of events.  Performing several experiments:

* [ ] Define a relation and show it is a partial order using hand-written properties
* [ ] Define a relation and show it is a partial order using the Coq relations infrastructure
* [ ] Define a partial order directly that is a PO by construction

Defined a trivial relation `lte` that is a relation over `event` that only incldues `btm` and `rtm`.  Will add adversary events when I prove this is a partial order.  Let's start simple.

9:38 PM - Looking at defining `S`, the specification of a measurement system and `E`, an execution that is accepted by `S`.  That will give us `A(S)` when defined.  Trying to captuer the distnction between `E` and `S` as defined.  `E` is a partial ordering like `S`, with some additional total ordering requirements for events that touch `o:O`.  Once that's clarified, we should be good to go.

Paul describes a measurement specification as an execution `S` that has no adversary events.  I'm not quite sure this is properly stated in the paper, but I completely agree with where it's going.  Exactly what the dog and I talked about on our run tonight.

10:25 PM - My definition of an execution being admitted in the Coq specification is wrong.  I believe it misses the surjective property specified in the definition.

## Notes - 18 August 2015 - 10:27 AM

`m` is now proven to be asymmetric, irreflexive, and RTM is not measured.  The latter is likely not necessary as RTM does not require measurement, but it is easy to prove and I'll leave the result where it is.

10:35 AM - One more goal for soundness that is exactly as expected.  Proved the case for `(m o o)` and now need the proof for cycles.  We know that `m` is asymmetric from `m`'s well-formedness proof and need to leverage that to show that `m*` is also asymmetric.

I have to wonder if there is an easier way to get these properties directly from `m` without looking at `m*`.  Come back to that later.  For right now, this proof should be easy to pop out using inversion.  Just have to slog through it.

1:01 PM - Thinking about the partial ordering model of a DAG it may be that we have a semi-lattice.  Regardless, this is clearly the right model.  Paul's definition of S admitting E is quite clear in capturing what I was thinking about.

1:59 PM - Looking at the Semantics document, I'm wondering if an acyclic condition on `M*` isn't the right way to capture what I keep talking about as irreflexive.  Same thing really, but acyclic is more descriptive of what we want - something can't be in it's own measurement chain.

12:22 AM - Moved to a finite Obj type to simplify proofs, but the transitive closure proof is still giving me fits.  Literally nothing changed.  I have to find an inconsistency that results from allowing reflection in the transitive closure.  I don't know what that inconsistency should be, but I think it's simple.

12:24 AM - Need to start using `M+` instead of `M*` for the transitive closure.  Got a bit sloppy there.

## Notes - 17 August 2015 - 9:11 AM

Basic Approach:

* [x] Define `M` and `M*` the transitive closure of `M`.
* [x] Define well-formedness of `M`. Irreflexive, nothing measures RTM.
* [x] Define example `m:M` and prove well-formedness
* [x] Define well-formedness of `M*`.  Irreflexive.
* [ ] Define example `m*:M*` and prove well-formedness
* [x] Define event type, `E`, to include boot-time measurement, run-time measurement, corruption, and repair
* [ ] Relate `M` to `rtm` events partial orders.  This is really quite trivial and may be as simple as a fold-like operation.
* [ ] Define event partial orders that include measurements, corruptions, and repairs.  Changing direction from simple sequences.
* [ ] {--Show that all corruptions are measured prior to associated repairs should repair occur.--} Show what corruptions go undetected and establish that they are acceptable.  The latter is human driven.
* [ ] The resulting measurement sequence is what must occur as a result of the attestation protocol and is a necessary condition on bundling.

If we can find a measurement sequence {++that allows only acceptable corruption events++}, we know what we must look for in the attestation bundling evidence. This binds bundling to ordering.

9:18 AM - The `noRTM` type has not proved useful in defining the `M` relation, but may prove useful defining well-formedness.  Still working on that.

11:58 AM - Paul brought up using partial orders rather than sequences to represent event DAGs. I think this is a great way to model the DAG in lieu of sequences. A new concept I've not thought of implementing directly in a prover.

11:13 PM - Why Joshua is right about partial orders.  Pretty simple really.  If we have a partial order of events - measurement and adversary - with a verified measurement property, all we have to do is show the attestation protocol implements the partial order and that bundling provides evidence it was respected during execution.  The partial order is all you need,

## Notes - 16 August 2015 - 6:40 PM

Working through Pierce suggests that one needs to construct a contradiction to prove the negation of a relation.  They do it using `assert` to propose the contradiction and then prove it from the hypothesis of the conclusion.  This should be pretty simple to try on the definition of `M`.

8:56 PM - it's not pretty simple.  There is a diffference between proving something *isn't* reflexive and that something *can't be* reflexive.  We're lookin at the former and no the latter.

9:05 PM - Completed the proof that `m` is well-formed - RTM is never measured and nothing measures itself.  Thus we know `m` is antireflexive.  These are properties of `m` that will be used in later proofs.

9:31 PM - First half of the well-formedness proof for `m*` is done using the `m` well-formedness result. Second part is not coing as well.

## Notes - 15 August 2015 - 6:05 PM

Trying to show a specific case, `~(m (obj 2) (obj 2))` from the example definition of `m` and can't get it to work.  Need to look and Pierce's chapter on relations and them tutorial writing on relations.  There must be a way to prove that a pair is not in a relation that I can't find.

It appears Pierce has some proofs of this type.  Next step is to go through Pierce's Relations chapter which should go quickly.

## Notes - 14 August 2015 - 12:39 PM

Something is wrong when proving that a relation does not hold.  Proving `~(m o o)` immediately gives a false proof goal with nothing to build a contradiction from. I think the relation definitions do not provide for negation of the relation.  Possibly one needs to negate the relation directly and look at that.

I'm not sure why we can't look at \\((o,o)\in m\\), but will look for that in the relations discussion that Pierce provides.

## Notes - 13 August 2015 - 10:46 AM

Working notes on the bundling theory and how it fits together. 

There are two structures to consider. First, `M`, captures a measured by relation over objects. It's transitive closure captures measurement chains. 

* `M` should not have cycles. That is captured by the irreflexivity of its transitive closure.
* `M` should not include RTM in its range.
 
A measurement in the transitive closure is rooted for o if  M is well-formed and (RTM.o) is in the closure. M is rooted if it is well formed and every o is rooted. This needs robe said better. 
 
I'm going to capture these properties in a dependent type over M. Likely using a subset type or capturing the property directly in a functions range type:
 
```
F(m:M):well_fomed(m)->T
```
 
1:08 PM	- Added RTM condition to `well_formed_m` and verified a simple example.

1:14 PM - Added a definition for irreflexivity and have already hit an interesting snag in the proof.  But, dependent types are to the rescue.

7:34 PM - Not so much to the rescue yet.  Still working on making the proof visible in the theory.

8:31 PM - The proof is jacked as is the thing being proved. I've done something wrong with the dependent type. Time to try a subset type.  Here's the original statement of well-formedness for m*:

```
Definition well_formed_m_star (m:M):((well_formed_m m) -> Prop) := 
  (fun p:(well_formed_m m) =>
     forall o : Obj, ((clos_trans Obj m) o o) -> False).
```

For some reason, `m` does not appear in the lemma as stated like this:

```
Lemma well_formed_m2: well_formed_m_star well_formed.
```

Where did `m` go?  Need to work on this to see what happened.

8:42 PM - Not so fast.  If we turn off `Set Implicit Arguments` the function requires an explicit `m`.  Still we have problems with the formulation of the proof that need to be addressed.

11:21 PM - Switched to a subset type.  Nothing changes much, but I did get the thing type checking.  Basically, I'm not completely suer of the relationship between the well-formedness relationships, nor am I sure a dependent type approach is the best way to capture conditions.
