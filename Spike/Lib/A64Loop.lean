/-
`correct_loop_a64` re-derived from the per-construct judgement.

The spinning reader of `Spike/Bridge/A64Loop.lean` (`l: ldar x2, [x0];
cbz x2, l` against `spin f = let r = load acq f in if r = 0 then spin f
else ret r`) as fragments of the relation:

* `HeadF`: at the loop head, the source at the body (`spinBody`, `f`
  bound);
* `MidF`: at the `cbz`, `x2` holding the value read, the source at the test
  with `r` bound to its low 64 bits;
* `ExitF`: past the `cbz`, the source at `ret r`.

The instructions as `Out` (`out_head`, `out_mid`): the `ldar` is the
source's load; the `cbz` is the test and the tail call (back to the head,
two local steps) or the test (to the exit, one local step). They compose
into the reader's segment `seg_reader : Seg progL lbl NumMS HeadF ExitF`
(`Seg.seq`, `Seg.loop`), and with its side conditions into
`Reader progL lbl F (HeadF ∨ MidF) ExitF` (`reader`), which
`Spike.Lib.correctS` consumes: `correct_loop_a64'` has the statement of
`correct_loop_a64`.
-/
import Spike.Lib.Thread
import Spike.Bridge.A64Loop

namespace Spike.Lib.A64Loop

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (SrcSem Target ValRep)
open Spike.Bridge (fTy fW envF flagA spinBody testTerm progL spinDecl srcInitL close_fTy asmOf)
open Spike.Bridge.A64 (F st0 sW shape regVal regs layoutΛ flagIn layoutΛ_wf)
open Spike.Bridge.A64Loop (lprog atL st1 Head Mid Exit exec_head exec_mid set_x0 set_x2 head_st1 regVal_x0
  regVal_x2)

/-- The flag's allocation is placed at `F`. -/
def lbl : WeakMem.AllocLabel → Option Nat := fun l => if l = 0 then some F.toNat else none

theorem valRep_fW {n : Nat} (h : ValRep lbl fW.val n) : n = F.toNat := by
  simpa [fW, TermRun.cst, Promises.TVal.mk0, ValRep, Scc.Sem.wordAddr, lbl, flagA] using h

/-! ## The fragments -/

/-- At the loop head; the source at the body. -/
def HeadF : Frag isaLSE2 := fun s c => Head s ∧ c = ⟨spinBody, envF, none⟩

/-- At the `cbz` with the value `v` read; the source at the test, `r` bound
to `v`'s low 64 bits. -/
def MidF : Frag isaLSE2 := fun s c =>
  ∃ v w, Mid v s ∧ w.val = .num (v.setWidth 64).toNat ∧ c = ⟨testTerm, ("r", .int, [w]) :: envF, none⟩

/-- Past the `cbz`; the source at `ret r`. -/
def ExitF : Frag isaLSE2 := fun s c =>
  ∃ v w, Exit v s ∧ w.val = .num (v.setWidth 64).toNat ∧ c = ⟨.ret (.var "r"), ("r", .int, [w]) :: envF, none⟩

/-! ## The source's local steps -/

theorem ls_test {w : TermRun.Word} {n : Nat} (hw : w.val = .num n) :
    LocalStep progL ⟨testTerm, ("r", .int, [w]) :: envF, none⟩
      ⟨if n = 0 then .tail "spin" [] (.var "f") else .ret (.var "r"), ("r", .int, [w]) :: envF, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht he _ _
  by_cases hn : n = 0
  · subst hn
    simp [TermRun.tstep, ht, he, testTerm, TermRun.evalAt, TermRun.lookupE, hw, TermRun.cst, Promises.TVal.mk0]
  · simp [TermRun.tstep, ht, he, testTerm, TermRun.evalAt, TermRun.lookupE, hw, TermRun.cst, Promises.TVal.mk0, hn]

theorem ls_tail (w : TermRun.Word) :
    LocalStep progL ⟨.tail "spin" [] (.var "f"), ("r", .int, [w]) :: envF, none⟩ ⟨spinBody, envF, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht he hσ hst
  simp [TermRun.tstep, ht, he, TermRun.enter, hg, progL, spinDecl, TermRun.evalAt, TermRun.lookupE, envF,
    TermRun.ol, hσ, hst]
  rw [close_fTy]

/-! ## The instructions -/

theorem loadTy_fTy : loadTy fTy = .int := rfl

/-- **The `ldar`** is the source's load. -/
theorem out_head {s : State} {c : Ctl} (h : HeadF s c) : Out progL lbl NumMS MidF s c := by
  obtain ⟨⟨r, rfl, h0⟩, rfl⟩ := h
  refine .load .acq F _ "r" (.var "f") testTerm fTy fW (exec_head r h0) rfl rfl ?_
    (fun v w' ⟨n, hn⟩ hval => ?_) ⟨_, rfl⟩
  · simp [fW, TermRun.cst, Promises.TVal.mk0, ValRep, Scc.Sem.wordAddr, lbl, flagA]
  · rw [hn] at hval
    obtain ⟨-, hv⟩ := hval
    exact ⟨v, w', ⟨_, rfl, (set_x0 r _).trans h0, set_x2 r _⟩, hn.trans (by rw [hv]), rfl⟩

/-- **The `cbz`** is the test and the tail call (back to the head) or the
test (to the exit). -/
theorem out_mid {s : State} {c : Ctl} (h : MidF s c) :
    Out progL lbl NumMS (fun s c => HeadF s c ∨ ExitF s c) s c := by
  obtain ⟨v, w, ⟨r, rfl, h0, h2⟩, hw, rfl⟩ := h
  refine .silent _ (if (v.setWidth 64).toNat = 0 then ⟨spinBody, envF, none⟩
    else ⟨.ret (.var "r"), ("r", .int, [w]) :: envF, none⟩)
    (exec_mid r) ?_ ?_
  · by_cases hz : (v.setWidth 64).toNat = 0
    · simp only [hz, ↓reduceIte]
      have := ls_test hw
      simp only [hz, ↓reduceIte] at this
      exact .step this (.single (ls_tail w))
    · simp only [hz, ↓reduceIte]
      have := ls_test hw
      simp only [hz, ↓reduceIte] at this
      exact .single this
  · rw [h2]
    by_cases hz : (v.setWidth 64).toNat = 0
    · have hz' : v.setWidth 64 = 0 := BitVec.eq_of_toNat_eq (by simpa using hz)
      simp only [hz', ↓reduceIte]
      exact .inl ⟨⟨r, rfl, h0⟩, rfl⟩
    · have hz' : v.setWidth 64 ≠ 0 := fun h => hz (by rw [h]; rfl)
      simp only [hz, hz', ↓reduceIte]
      exact .inr ⟨v, w, ⟨r, rfl, h0, h2⟩, hw, rfl⟩

/-- **The reader's segment**, composed: the `ldar` then the `cbz`, looped on
the back edge. -/
theorem seg_reader : Seg progL lbl NumMS HeadF ExitF :=
  Seg.loop (Seg.seq (Seg.step fun _ _ => out_head) (Seg.step fun _ _ => out_mid))

/-! ## The consumer's inputs -/

/-- **The reader**, its invariant the head and the test. -/
theorem reader : Reader progL lbl F (fun s c => HeadF s c ∨ MidF s c) ExitF where
  out s c h := by
    rcases h with h | h
    · exact (out_head h).mono fun s c h => .inl (.inr h)
    · exact (out_mid h).mono fun s c h => h.elim (fun h => .inl (.inl h)) .inr
  fin := by
    rintro _ _ ⟨v, w, ⟨r, rfl, -, -⟩, -, -⟩
    exact Spike.Bridge.A64.exec_end (by show ((0x100008 : Int64) == 0x100000 + 8) = true; decide)
  noStore := by
    rintro s c (⟨-, rfl⟩ | ⟨v, w, -, -, rfl⟩) x a b e h <;> simp [spinBody, testTerm] at h
  noXchg := by
    rintro s c (⟨-, rfl⟩ | ⟨v, w, -, -, rfl⟩) x sa u v e ⟨-, ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, _, _, _, _, _, h, -⟩⟩ <;>
      simp [spinBody, testTerm] at h
  noAlloc := by
    rintro s c (⟨-, rfl⟩ | ⟨v, w, -, -, rfl⟩) x a τ e h <;> simp [spinBody, testTerm] at h
  flag := by
    rintro s c (⟨-, rfl⟩ | ⟨v, w, -, -, rfl⟩) x a e h
    · simp only [spinBody, Expr.let_.injEq, Op.load.injEq, true_and] at h
      obtain ⟨-, rfl, -⟩ := h
      rfl
    · simp [testTerm] at h
  addr _ h := valRep_fW h

theorem val64_toNat (v : Val) : ((v.setWidth 64).setWidth 128 : Val).toNat = (v.setWidth 64).toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (v.setWidth 64).isLt; omega)

/-- The `cbz`'s value as a 64-bit value. -/
theorem val64 (v : Val) : ((v.setWidth 64).setWidth 128 : Val).toNat < 2 ^ 64 ∧
    ((v.setWidth 64).setWidth 128 : Val).setWidth 64 = v.setWidth 64 := by
  have h := (v.setWidth 64).isLt
  have h1 : ((v.setWidth 64).setWidth 128 : Val).toNat = (v.setWidth 64).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨h1 ▸ h, BitVec.eq_of_toNat_eq ?_⟩
  rw [BitVec.toNat_setWidth, h1, BitVec.toNat_setWidth]
  exact Nat.mod_mod _ _

/-- **Where the fragments place the source words**: `x0` the flag's
address, `x2` the value read. -/
theorem place : Place regVal F st0 sW (RegId.x 0) (RegId.x 2) (fun s c => HeadF s c ∨ MidF s c) ExitF where
  f0 := regs.f0
  fW := regs.fW
  frame := by
    rintro s c ((⟨⟨r, rfl, h0⟩, rfl⟩ | ⟨v, w, ⟨r, rfl, h0, h2⟩, hw, rfl⟩) | ⟨v, w, ⟨r, rfl, h0, h2⟩, hw, rfl⟩)
    · exact ⟨regVal_x0 r _ h0, .inl rfl⟩
    · refine ⟨regVal_x0 r _ h0, .inr ⟨(v.setWidth 64).setWidth 128, w, rfl, ?_, (val64 v).1, ?_⟩⟩
      · rw [hw, (val64_toNat v)]
      · rw [(val64 v).2]; exact (regVal_x2 r _).trans h2
    · refine ⟨regVal_x0 r _ h0, .inr ⟨(v.setWidth 64).setWidth 128, w, rfl, ?_, (val64 v).1, ?_⟩⟩
      · rw [hw, (val64_toNat v)]
      · rw [(val64 v).2]; exact (regVal_x2 r _).trans h2

theorem head_init : HeadF st1 ⟨spinBody, envF, none⟩ := ⟨head_st1, rfl⟩

theorem srcInit_eq : srcInitS ⟨spinBody, envF, none⟩ = srcInitL := rfl

variable {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- **`correct_loop_a64` from the judgement**: the statement of
`Spike.Bridge.A64Loop.correct_loop_a64`, proved by `Spike.Lib.correctS` from
the reader's fragments. -/
theorem correct_loop_a64' (pl : State → BitVec 64 → Option (BitVec 64)) (B : Scc.Sem.Budget) :
    Scc.Sem.Correct (Target.ofBase isaLSE2 Arch.armv8 regVal pl) (SrcSem.ofStep progL k arch (· = srcInitL))
      layoutΛ B (asmOf st0 st1 F) :=
  correctS Arch.armv8 reader shape.toWShape (.inl head_init) place flagIn layoutΛ_wf B rfl

end Spike.Lib.A64Loop
