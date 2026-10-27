/-
**A lane store's site in the source** (ISA-neutral): at the node of `let x
= xchgAt b j v` (`NodeJE` at `ofEnv2 env`, the buffers `EnvB`), with `b` a
buffer of the walk and `j` a literal in range (`XchgB`), the source is at
an exchange site (`XchgSite`) of the element's address `sa`; the element
type is one word (`elem2`); the lowering's slot address (`slotAddr`) is
`b`'s base register at displacement `8 * k`, and the base's value plus it
is `sa`'s word address (no wrap, `LblRoom`). The stored atom `v`'s word is
its operand's value.

- `bufElem_eq`: the lowering's and the source's buffer element agree;
- `xchg_site`: the site, the element type, the address;
- `xchg_val`: the stored word;
- `atomV_fresh`: an atom's registers are off `regName x n` (`Fresh`);
- `toNat_add_ofInt8`: a base value plus the displacement `8 * k`, no wrap.
-/
import Spike.Lib.Src.NJLB
import Spike.Lib.Src.XchgB
import Spike.Lib.Src.GroupPl

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv sevalAt lookupS WordPl WordsRep WordRep LocRep group)
open Scc.Sem (ValRep)
open Scc.Lower (LitV elem2)
open Spike.Lib.LowerShape (refO slotAddr)
open Scc.Lower.Inv (atomV regName)

theorem bufElem_eq (t : Ty) : Scc.Lower.bufElem t = TermRun.bufElem t := by
  unfold Scc.Lower.bufElem TermRun.bufElem
  rfl

/-- **A base plus a displacement `8 * k`** (as the machine adds it) that does
not wrap. -/
theorem toNat_add_ofInt8 {vb : BitVec 64} {k : Nat} (h : vb.toNat + 8 * k < 2 ^ 64) :
    (vb + BitVec.ofInt 64 (8 * (k : Int))).toNat = vb.toNat + 8 * k := by
  have e : (8 * (k : Int)) = ((8 * k : Nat) : Int) := by omega
  rw [e, BitVec.ofInt_natCast, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

/-- **An atom's registers are off `regName x n`** (`Fresh`). -/
theorem atomV_fresh {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) {a : At} {t : Ty}
    {ws : List Scc.IR.Operand} (ha : atomV env a = some (t, ws)) (x : String) :
    ∀ o ∈ ws, ∀ r, o = .reg r → r ≠ regName x n := by
  intro o ho r hr
  cases a with
  | var y =>
    simp only [atomV, Option.map_eq_some_iff] at ha
    obtain ⟨⟨z, t', ws'⟩, hf, he⟩ := ha
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h _ (List.mem_of_find?_eq_some hf) o ho r hr x n (Nat.le_refl n)
  | lit k =>
    simp only [atomV] at ha
    split at ha
    · cases ha
    · simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨-, rfl⟩ := ha
      simp only [List.mem_singleton] at ho
      subst ho; cases hr
  | unit =>
    simp only [atomV, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨-, rfl⟩ := ha
    cases ho

/-- **The stored atom's word**: one source word (at the atom's source type
`tv'`, `tv` up to the buffers' literal lengths), its operand's value
representing it. -/
theorem xchg_val {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int} {t : Expr}
    {env : Scc.Lower.Env} {sl : Int → BitVec 64} {c1 : Ctl} (hj : NodeJE lbl rs t (ofEnv2 env) sl c1)
    (hg : GrpL env) {v : At} {tv : Ty} {w : Scc.IR.Operand} (hav : atomV env v = some (tv, [w])) :
    ∃ tv' wv n, TermRun.evalAt c1.env v = some (tv', [wv]) ∧ opdVal rs sl w = some n ∧ ValRep lbl wv.val n := by
  have hs := sevalAt_ofEnv2G_one hg hav
  obtain ⟨tv', ws, he, -, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hs
  match ws, hw with
  | [wv], ⟨⟨n, hn, hv⟩, _⟩ => exact ⟨tv', wv, n, he, hn, hv⟩

/-- **A lane store's site**: at the node of `let x = xchgAt b j v` with `b`
a buffer of the walk and `j` a literal `k` in range (`XchgB`), the source's
control `c1` is at the exchange site of `sa`, element `k` of `b`'s label,
with no hold; the element type `u` is one word (`elem2`); the slot address
the lowering builds is at displacement `8 * k` from `b`'s base register
`rb`, whose value `vb` plus `8 * k` is `sa`'s word address, below `2^64`
(`LblRoom`); `k` is within the label's size (`EnvB`'s `lsize`). -/
theorem xchg_site {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
    {lits : List (String × LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {x : String} {b j v : At} {e : Expr} {env : Scc.Lower.Env}
    {sl : Int → BitVec 64}
    {c1 : Ctl} (hj : NodeJE lbl rs (.let_ x (.xchgAt b j v) e) (ofEnv2 env) sl c1)
    (hb : EnvB lits cs bufs L sm lsize c1.env) (hX : XchgB bufs b j) (hg : GrpL env) (hroom : LblRoom lbl)
    {t : Ty} {bw : List Scc.IR.Operand} {rb : Scc.IR.Reg} {o : UInt64} {tj : Ty} {iv : UInt64} {μ : Mode}
    {u : Ty} {nu mu : Nat} {s1 : Bool × Nat}
    (hab : atomV env b = some (t, bw)) (hrf : refO bw = some (.reg rb, .imm o))
    (haj : atomV env j = some (tj, [.imm iv])) (hbe : Scc.Lower.bufElem t = some (μ, u))
    (hro : Scc.Obj.regOf u = some (nu, mu)) (hsl : Scc.Obj.slots u 0 0 = some [s1]) (ob : Scc.ObjLayout) :
    elem2 u = true ∧ ∃ (sa : WeakMem.Address) (vb k : Nat), XchgSite c1 x sa u v e ∧ c1.hold = none ∧
      opdVal rs sl (.reg rb) = some vb ∧
      (slotAddr ob rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1).disp = 8 * (k : Int) ∧ k < 2 ^ 28 ∧
      Scc.Sem.wordAddr lbl sa = some (vb + 8 * k) ∧ lbl sa.label = some vb ∧ k < lsize sa.label ∧
      vb + 8 * k < 2 ^ 64 ∧
      ValRep lbl (.loc sa 0) (vb + 8 * k) := by
  obtain ⟨b', k, nB, rfl, rfl, hlk, hkn, hn28⟩ := hX
  obtain ⟨t', u', l, hle, hbe', hel, -, -, hnz⟩ := hb.2.1 b' nB hlk
  obtain ⟨pls, hgp, hsv⟩ := sevalAt_ofEnv2G hg hab
  have hpl := group_buf hbe hrf hgp
  subst hpl
  obtain ⟨t'', ws, hle2, hE, hwr⟩ := hj.2.2 b' t _ hsv
  rw [hle] at hle2
  simp only [Option.some.injEq, Prod.mk.injEq] at hle2
  obtain ⟨rfl, rfl⟩ := hle2
  obtain ⟨⟨vb, vo, hvb, hvo, hLR⟩, -⟩ := hwr
  simp only [TermRun.cst, LocRep] at hLR
  obtain ⟨-, hlv, hvo0⟩ := hLR
  simp only [opdVal, Option.some.injEq] at hvo
  have ho0 : o = 0 := by
    simp only [Nat.mul_zero] at hvo0
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_zero]; omega
  subst ho0
  rw [bufElem_eq, ← Spike.Lib.Form.bufElem_eraseLen, ← hE, Spike.Lib.Form.bufElem_eraseLen, hbe'] at hbe
  simp only [Option.some.injEq, Prod.mk.injEq] at hbe
  obtain ⟨rfl, rfl⟩ := hbe
  simp only [atomV] at haj
  split at haj
  · cases haj
  · rename_i hk64
    simp only [Option.some.injEq, Prod.mk.injEq, Scc.Lower.imm, List.cons.injEq, Scc.IR.Operand.imm.injEq,
      and_true] at haj
    obtain ⟨-, rfl⟩ := haj
    have hA := hroom l vb hlv
    -- the element type is one scalar word: slot `(false, 0)`, layout `(1, 0)`
    have hu : TermRun.accs u' = some [.one] ∧ s1 = (false, 0) ∧ nu = 1 ∧ mu = 0 := by
      cases u' <;> simp_all [elem2, Scc.Obj.slots, Scc.Obj.regOf, TermRun.accs]
    obtain ⟨hacc, rfl, rfl, rfl⟩ := hu
    refine ⟨hel, TermRun.offs ⟨l, 0⟩ k, vb, k, ?_, hj.2.1, hvb, ?_, by omega, ?_, ?_, ?_, by omega, ?_⟩
    · refine ⟨hacc, .inr ⟨.var b', .lit k, t', TermRun.cst (.loc ⟨l, 0⟩ 0), .intS (.lit k),
        [TermRun.cst (.num k)], .own, ⟨l, 0⟩, k, hj.1, hle, rfl, hbe', rfl, rfl, rfl⟩⟩
    · have hw : (0 + UInt64.ofNat k * UInt64.ofNat (Scc.Obj.stride 1 0)).toNat = 8 * k := by
        simp only [Scc.Obj.stride, Scc.Obj.offWord, Scc.Obj.halfBits]
        rw [UInt64.zero_add, UInt64.toNat_mul]
        simp only [UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [slotAddr, Bool.false_eq_true, ↓reduceIte, Scc.Obj.halfBits, hw]
      omega
    · simp [Scc.Sem.wordAddr, TermRun.offs, hlv]
    · exact hlv
    · show k < lsize l; omega
    · exact ⟨by decide, vb + 8 * k, by simp [Scc.Sem.wordAddr, TermRun.offs, hlv], rfl⟩

end Spike.Lib.LowerNode
