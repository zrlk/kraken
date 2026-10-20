/-
Program-agnostic obligations of a `ThreadRuleRX` (`SLR/ThreadRuleX.lean`),
parametric in the rule's invariants; the spinlock and MP rules
(`SwpRuleX`, `X64SpinRule`, `MpWriter`) are specialisations.

- `PrepayObG A tid J`: the `ThreadRuleRX.prepay` field for the invariant `J`;
- `LiftObG A tid J₀ J`: the lift of a cell proof from a state with no own
  pending promise, an `EraseWPR` into `WpPostR J₀`, to the dead-branch form,
  an `EraseWPRD` into `WpPostR J`;
- `PendInMem`, `OwnPendOf`, `InvXOf`: the usual shape of the instance
  invariant `J = J₀ ∧ PendInMem ∧ OwnPendOf Q` (pending marks are messages,
  and an own pending promise satisfies the program's `Q`);
- `EnvExt.read?`: reads survive environment extensions;
- `liftOb_invXOf`: the lift holds for every invariant of that shape (the
  former `swp_lift` / `X64Spin` lift / `mp_lift` proof, once).
-/
import Kraken.Promising.SLR.ThreadRuleXLift

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising

variable {I : ISA}

/-- **`ThreadRuleRX.prepay` for an invariant `J`.** -/
def PrepayObG (A : Arch) (tid : Nat) (J : Prop → Config I → Res → Ghost → Prop) : Prop :=
  ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), J cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      J (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **The lift obligation** from `J₀` (a cell proof at a state with no own
pending promise) to `J` (the dead-branch form of `ThreadRuleRX.wp`). -/
def LiftObG (A : Arch) (tid : Nat) (J₀ J : Prop → Config I → Res → Ghost → Prop) : Prop :=
  ∀ {cl' : Prop} {c : Config I} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), c.threads[tid]? = some t → Erase (setRes rF tid r) g (fun _ => True) c →
    c.MachInv → (∀ ts ∈ t.prom, ts ∉ g.pend) →
    tree.EraseWPR A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR J₀ cl' c tid r g t) r g (ctx₀ t tid c.mem) →
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR J cl' c tid r g t) r g (ctx₀ t tid c.mem)

/-- The pending marks are messages of `m`. -/
def PendInMem (g : Ghost) (m : Memory) : Prop := ∀ ts ∈ g.pend, ts ≤ m.last

/-- Every own pending promise `ts` of thread `tid` satisfies `Q`. -/
def OwnPendOf (Q : Thread I → Config I → Res → Ghost → Time → Prop) (tid : Nat) (c : Config I) (r : Res)
    (g : Ghost) : Prop :=
  ∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend → Q t c r g ts

/-- The instance invariant built from `J₀`: `J₀`, the pending marks are
messages, and own pending promises satisfy `Q`. -/
def InvXOf (J₀ : Prop → Config I → Res → Ghost → Prop) (Q : Thread I → Config I → Res → Ghost → Time → Prop)
    (tid : Nat) (cl : Prop) (c : Config I) (r : Res) (g : Ghost) : Prop :=
  J₀ cl c r g ∧ PendInMem g c.mem ∧ OwnPendOf Q tid c r g

/-- **The lift for every `InvXOf` invariant**: along the run of a cell from
a state with no own pending promise the memory grows and no promise is
added, so after the instruction the pending marks (`g'.pend ⊆ g.pend`) are
messages and none is an own promise (`OwnPendOf`, vacuously). -/
theorem liftOb_invXOf (A : Arch) (tid : Nat) (J₀ : Prop → Config I → Res → Ghost → Prop)
    (Q : Thread I → Config I → Res → Ghost → Time → Prop) : LiftObG A tid J₀ (InvXOf J₀ Q tid) := by
  intro cl' c r g rF t tree ht E _ hnp h
  refine EvTree.EraseWPR.toD_run (fun s r' g' cx hJ hP => ?_) tree r g _ RunJ.ctx₀ h
  obtain ⟨hg, hkeep, hnew, hacq, hown, hfin⟩ := hP
  refine ⟨hg, hkeep, hnew, hacq, hown, fun t' ht' hd => ⟨hfin t' ht' hd, ?_, ?_⟩⟩
  · intro ts hts
    exact Nat.le_trans (E.pend_le (hnew ts hts)) hJ.1
  · intro t'' ht'' ts hts hpd
    rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht)] at ht''
    simp only [ite_true, Option.some.injEq] at ht''
    subst ht''
    rw [(finishInstr_relKey ht').1] at hts
    exact absurd (hnew ts hpd) (hnp ts (hJ.2 ts hts))

/-- A read of a memory is a read of every environment extension. -/
theorem EnvExt.read? {tid : Nat} {c c₁ : Config I} (he : EnvExt tid c c₁) {l : Loc} {ts : Time} {v : Val}
    (h : c.mem.read? l ts = some v) : c₁.mem.read? l ts = some v := by
  have hpre : c.mem.Prefix c₁.mem := ⟨he.1, he.2.1⟩
  have hle : ts ≤ c.mem.last := by
    unfold Memory.read? at h
    split at h
    · next h0 => rw [h0]; exact Nat.zero_le _
    · split at h
      · next w hw => exact c.mem.last_le_of_get?_eq_some hw
      · cases h
  rw [hpre.read? hle]; exact h

end Kraken.Promising.SLR
