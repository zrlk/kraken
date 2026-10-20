import WeakCore.TermIni

/-!
# Box payment: `RunAgreeW.pay` from the box facts L1–L3

A start box's payload reference, inspectable at the certificate environment
`E2` at the word's view, names a `PlantG` label.  `FrBound_inspM` (the box's
frontier is below the start size) makes the label a start label; a published
cell or a box is in `PlantG`; a private start cell is own (`hfp`), so by (L3)
the box is the certifier's own, whose frontier (L2) is at most the start
`vWr` `v0`, at most any frontier set in the run (`FrBound` (i)); but the
word's view is below the box's frontier (L1): no such inspection.

The box facts are hypotheses here, on the start environment `E0` only
(boxes are frozen); they come from the global invariant (`SysInvN` start
clauses):
* (L1) `hL1`: a payload reference's view is below its box's frontier;
* (L2) `hL2`: an own box's frontier is at most the start `vWr`;
  `hLn`: every box's frontier is at most the start memory size;
* (L3) `hL3`: a payload reference to a private cell names a cell of the box's owner.
-/

namespace TermIni

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermFul TermIniStep TermTyped TermGlob
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **`RunAgreeW.pay` from L1–L3.** -/
theorem runAgree_payW {E0 E2 : TEnv} {Lp : AllocLabel → Prop} {n v0 : Nat}
    (hfb : FrBound E0 (n + 1) v0 E2)
    (hsto : ∀ l c, E0.sto l = some c → E2.sto l = some c)
    (hbox : ∀ l B, E0.box l = some B → E2.box l = some B)
    (hdisj : ∀ l B, E2.box l = some B → E2.sto l = none)
    (hL : ∀ l, Lp l → ∃ c, E0.sto l = some c)
    (hfp : ∀ a cl, E0.sto a = some cl → E0.pfr a = none → cl.owner = some E0.tid)
    (hL1 : ∀ l B, E0.box l = some B → ∀ w ∈ B.pay, ∀ (a' : Address) (g : Nat), w.val = .loc a' g →
      w.view < B.fr)
    (hL2 : ∀ l B, E0.box l = some B → B.own = E0.tid → B.fr ≤ v0)
    (hLn : ∀ l B, E0.box l = some B → B.fr ≤ n)
    (hL3 : ∀ l B, E0.box l = some B → ∀ w ∈ B.pay, ∀ (a' : Address) (g : Nat), w.val = .loc a' g →
      ∀ c, E0.sto a'.label = some c → E0.pfr a'.label = none → c.owner = some B.own) :
    ∀ a B, PlantG E0 Lp a → E2.box a = some B → ∀ w ∈ B.pay, ∀ (a' : Address) (g : Nat),
      w.val = .loc a' g → InspM E2 a'.label w.view → PlantG E0 Lp a'.label := by
  intro a B hG hB w hw a' g hv hi
  -- the outer label is a start box
  have hB0 : E0.box a = some B := by
    have hsn : ∀ c, E0.sto a = some c → False := fun c hc => by
      have e := hsto a c hc; rw [hdisj a B hB] at e; cases e
    rcases hG with ⟨c, f, hc, -⟩ | hLa | ⟨B0, hB0⟩
    · exact (hsn c hc).elim
    · obtain ⟨c, hc⟩ := hL a hLa; exact (hsn c hc).elim
    · rw [hbox a B0 hB0] at hB; cases hB; exact hB0
  have h1 := hL1 a B hB0 w hw a' g hv
  have hlt : w.view < n := Nat.lt_of_lt_of_le h1 (hLn a B hB0)
  rcases FrBound_inspM hfb hi hlt with ⟨c0, hc0⟩ | ⟨B1, hB1⟩
  · rcases hpf : E0.pfr a'.label with _ | f0
    · -- a private start cell: own, so the box is own; no inspection
      have ho := hL3 a B hB0 w hw a' g hv c0 hc0 hpf
      rw [hfp _ c0 hc0 hpf] at ho
      have hown : B.own = E0.tid := (Option.some.inj ho).symm
      have h2 := hL2 a B hB0 hown
      exfalso
      rcases hi with ⟨c, f, hc, hf, hle⟩ | ⟨B', hB', -⟩
      · have h3 := hfb.1 a'.label c f hpf hc hf
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h3 hle) (Nat.lt_of_lt_of_le h1 h2))
      · have e := hsto _ c0 hc0; rw [hdisj _ B' hB'] at e; cases e
    · exact .inl ⟨c0, f0, hc0, hpf⟩
  · exact .inr (.inr ⟨B1, hB1⟩)

end TermIni

#print axioms TermIni.runAgree_payW
