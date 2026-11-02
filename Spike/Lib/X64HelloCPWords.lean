/-
**`ChildPrem`'s slice words at the clone's data** (x86-64; the twin of `Spike/Lib/HelloCPWords.lean`, same names):
at main's `clone`, under `VBufR` (where the slice's buffer label is `lBH`, `X64HelloNewBuf.clonePreH_labels`), the
packet's words `w0 w1 w2` (`.loc ⟨lBH, 0⟩ 0`, `.num 2`, `.num 13`) are represented by the clone's `wordsX th` at `w0`,
`w2`, `w3` (`X64HelloHv012.hv012_of_clone` for the buffer, `X64HelloPreA.sl_clone` for the two numbers).

- `hv012_clone`: `ChildPrem`'s `hv0`, `hv1`, `hv2` at `ClonePreH`'s `lbl`.
- `hv012_preRH`: the same at `PreRH`, at the record's placement `(SR w).lbl` (`X64HelloSpawnR.lbl_clone`).

**Unlike AArch64**, `wordsX th`'s `w0`, `w2`, `w3` are main's `%r12`, `%r13`, `%r14` (AArch64: `x9`, `x11`, `x12`),
and `ClonePreH` has no label prefix `pfx`.
-/
import Spike.Lib.X64HelloHv012
import Spike.Lib.X64HelloNewBuf
import Spike.Lib.X64HelloChildWords
import Spike.Lib.X64HelloChildX

namespace Spike.Lib.X64HelloCPWords

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (ValRep)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64HelloPreA (ClonePreH)
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloOkW (lBH)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (wordsX)

/-- **The slice words at the clone** (module doc): `hv0` at `w0`, `hv1` at `w2`, `hv2` at `w3` of `wordsX th`. -/
theorem hv012_clone {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (hv : Spike.Lib.X64HelloVBuf.VBufR s)
    (h : ClonePreH Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th])
    {w0 w1 w2 : TermRun.Word} (h0 : w0.val = .loc ⟨lBH, 0⟩ 0) (h1 : w1.val = .num 2) (h2 : w2.val = .num 13) :
    ValRep lbl w0.val (wordsX th).w0.toNat ∧ ValRep lbl w1.val (wordsX th).w2.toNat ∧
      ValRep lbl w2.val (wordsX th).w3.toNat := by
  obtain ⟨th', th0, hd, l, b, m, n, hth', hs, hS, hb, -, -⟩ := Spike.Lib.X64HelloHv012.hv012_of_clone h
  obtain rfl : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨th0', hd', l', lb, ws, hs', hS', hh, rfl, -, -⟩ := Spike.Lib.X64HelloNewBuf.clonePreH_labels hv h
  obtain rfl : th0 = th0' := by
    rw [hs] at hs'
    exact List.singleton_inj.mp (congrArg Array.toList hs')
  have hws : ws = [b, m, n] := by
    have e := hS'.2.2.2.2.1
    rw [hS.2.2.2.2.1] at e
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at e
    exact e.symm
  subst hws
  simp only [List.head?_cons, Option.some.injEq] at hh
  have hbv : b.val = .loc ⟨lBH, 0⟩ 0 := by rw [hh]; rfl
  obtain ⟨h11, h12⟩ := Spike.Lib.X64HelloPreA.sl_clone h hth
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, ← hbv]
    exact hb
  · rw [h1]
    exact ⟨by decide, h11⟩
  · rw [h2]
    exact ⟨by decide, h12⟩

section Pre

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → Spike.Lib.Inv2Core.SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Spike.Lib.Inv2Core.Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : Spike.Lib.X64WakeM0.MSide ι}
  {D : Spike.Lib.X64HelloW1.WSideH ι} {r0 r1 : ι → Scc.Sem.Range} {Λ : Scc.Sem.Layout} {w : ι} {d : Cfg}
  {th : Thread isa} {stack : Nat} {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
  {l : WeakMem.AllocLabel}

/-- **The slice words at `PreRH`**, at the record's placement (`hCP`'s `ChildPrem` placement). -/
theorem hv012_preRH (hv : Spike.Lib.X64HelloVBuf.VBufR s)
    (hR : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l)
    {w0 w1 w2 : TermRun.Word} (h0 : w0.val = .loc ⟨lBH, 0⟩ 0) (h1 : w1.val = .num 2) (h2 : w2.val = .num 13) :
    ValRep (SR w).lbl w0.val (wordsX th).w0.toNat ∧ ValRep (SR w).lbl w1.val (wordsX th).w2.toNat ∧
      ValRep (SR w).lbl w2.val (wordsX th).w3.toNat := by
  obtain ⟨X, hC⟩ := hR.clone
  rw [Spike.Lib.X64HelloSpawnR.lbl_clone hR]
  exact hv012_clone hv hC hR.pre.threads h0 h1 h2

end Pre

end Spike.Lib.X64HelloCPWords

/-- info: 'Spike.Lib.X64HelloCPWords.hv012_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCPWords.hv012_clone

/-- info: 'Spike.Lib.X64HelloCPWords.hv012_preRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloCPWords.hv012_preRH
