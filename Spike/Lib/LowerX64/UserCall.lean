/-
**The user `main` as `scc_rt_main`'s user function** (x86-64): the
interface `UserCallW` (`Spike/Lib/Rt/X64Main.lean`) inside the consumer's
facts, from the lowered function's segment `fn0_seg`
(`Spike/Lib/LowerX64/Fn.lean`) held back at the source start
(`SegW.lag`, `Spike/Lib/SegLag.lean`). The twin of
`Spike/Lib/LowerA64/UserCall.lean`.

The source control at the call is the start's (`X64Consumer.c0`, a tail
call into `main`): `fn0_seg`'s entry invariant holds there, its body's
`NJ` a local run (the start's step, `start_step_main`) away
(`nj_start`). The segment's obligations are inside `BodyW0`
(`proW_body0`, `hWb_of`, `hWs_of`) and, held back at the start, inside
`SFacts`; its return reaches the return address with the start control
and the return value related by `UPost`; its overflow abort is the
premise `hab` (from the held-back abort block, `seg_localW_lag`).

- `RetV`, `UPost`: a control at `ret` of a one-word atom valued `v`;
  the start control with a local run to one (the return-value contract).
- `start_step_main`, `nj_start`: the start's step into `main`, `NJ` at the
  start.
- `addr_toNat_mod8`, `stackOff_rbR`: an 8-aligned base moved by a multiple
  of 8 stays 8-aligned; the words of `rS` off a region are off its rebased
  region `rbR` (the same bytes).
- `userCallW_of_fn`: the interface from the function's code facts.

Where x86-64 differs from AArch64:
- the callee's region is based at the entry `%rsp` (the return address's
  cell, `hi = 8`), `8` below the caller's frame of `Z` and its saved
  `%rbp`; its base is 8-aligned from the caller's (`hR8`, `hZ8`;
  AArch64: `UserCallW` gives a 16-aligned base);
- the body and its exits are in `rbR` of it (`fn0_seg`), so the return's
  exit is moved back to the callee's region (`at_of_rbR`), `%rsp` past the
  return address (`uNx`: `g.sp + 8`, from the entry's `%rsp` at the base);
- the limit room is the function's frame `ZU = fr.size` below the return
  address's cell, and the depth `D` holds the frame and the saved `%rbp`
  (`hD`).
-/
import Spike.Lib.LowerX64.Main
import Spike.Lib.LowerX64.UserW
import Spike.Lib.X64StubFacts
import Spike.Lib.Rt.X64Main

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW)
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.Rt.X64 (Lays endOf)
open Scc.Sem (Marks Range ValRep)
open Spike.Lib.Form (SEnv lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 Res)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl K0)
open Spike.Lib.X64.Rt (InstOk UserCallW uN0 uNx)
open Spike.Lib.X64.Flow.Ret0 (StackOff CallerCells WcG LimOk limA)

/-! ## The return-value contract -/

/-- **A control at the return of a one-word atom valued `v`** (a number). -/
def RetV (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) (v : BitVec 64) : Prop :=
  ∃ a t w, c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, [w]) ∧ (∃ n, w.val = .num n) ∧
    ValRep lbl w.val v.toNat

/-- **The user function's post**: the source control is the start `c0`
(held back), from which a local run reaches the return of `v` (`RetV`). -/
def UPost (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c0 c : Ctl) (v : BitVec 64) : Prop :=
  c = c0 ∧ ∃ c', LocalRun p c0 c' ∧ RetV lbl c' v

/-! ## The start -/

/-- **The source start's step into `main`** (`hd`): its body, its argument
bound to the start's unit. -/
theorem start_step_main {p : Prog} {d : Decl} (hd : p.find? (·.name == "main") = some d) :
    LocalStep p Spike.Lib.X64Consumer.c0 ⟨d.body, [(d.arg, TermRun.close [] d.argTy, [])], none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht he hs _
  simp only [TermRun.tstep, ht, TermRun.enter, hg, hd, he, Spike.Lib.X64Consumer.c0, TermRun.evalAt,
    TermRun.lookupE, List.find?, TermRun.ol, Option.map, Option.toList]
  obtain ⟨⟩ := th
  simp only at hs
  subst hs
  simp

/-- **`main`'s body node at the start**: a local run (the start's step)
reaches `main`'s body with its `Unit` argument, no word. -/
theorem nj_start {p : Prog} {d : Decl} (hd : p.find? (·.name == "main") = some d) (hu : d.argTy = .unit)
    {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} :
    NJ p lbl rs d.body (ofEnv [(d.arg, .unit, [])]) sl Spike.Lib.X64Consumer.c0 := by
  refine ⟨_, .single (start_step_main hd), ⟨rfl, rfl, ?_⟩, ?_⟩
  · intro x t pls hl
    simp only [ofEnv, List.map, lookupS] at hl
    by_cases hx : d.arg = x
    · subst hx
      simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨[], by simp [TermRun.lookupE, hu]; rfl, trivial⟩
    · simp [hx] at hl
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro w hw; cases hw

/-! ## Regions -/

/-- **An 8-aligned base moved by a multiple of 8 is 8-aligned.** -/
theorem addr_toNat_mod8 (R : Region) (hb : R.base.toNat % 8 = 0) {k : Int} (hk : k % 8 = 0) :
    (R.addr k).toNat % 8 = 0 := by
  rw [Region.addr, BitVec.toNat_add, BitVec.toNat_ofInt, Nat.mod_mod_of_dvd _ (⟨2 ^ 61, by decide⟩ : 8 ∣ 2 ^ 64)]
  have ht : 0 ≤ k % ((2 ^ 64 : Nat) : Int) ∧ k % ((2 ^ 64 : Nat) : Int) % 8 = 0 := by
    rw [show ((2 ^ 64 : Nat) : Int) = 18446744073709551616 from rfl]; omega
  omega

/-- **The words of `rS` off a region are off its rebased region** (`rbR`:
the same bytes, based `8` lower). -/
theorem stackOff_rbR {rS : Range} {R : Region} {m : MachineData} (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 0 ≤ R.hi)
    (h : StackOff rS R m) : StackOff rS (rbR R) m := by
  intro a h8 ha ha7 hout
  have hb := Region.callee_base (hi' := R.hi + 8) hR (show R.lo ≤ -8 + (R.lo + 8) by omega) (by omega)
    (show (-8 : Int) < R.hi by omega)
  simp only [rbR] at hout
  simp only [Region.callee] at hout hb
  exact h a h8 ha ha7 (by omega)

/-! ## The interface -/

section Call

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **The user `main` is `scc_rt_main`'s user function inside `SFacts`**
(`UserCallW`, write tail `Dt`, limit room `ZU` its frame, post `UPost`):
for an `Accepted0` program `[d]` (`hd`) whose `main` lowers to `r` (`hr`)
at a valid frame `fr` (`hf`, `h1`), its prologue at the listing's sizes
and body in `cells` (`hpro`, `hbody`), an instance's facts (`hI`), the
caller's region's base and frame 8-aligned (`hR8`, `hZ8`), the callee's
depth `D` holding the frame and the saved `%rbp` (`hD`, `hD8`), the
body's and the prologue's phase facts at the return address `ra` (`hphB`,
`hphP`), the start's facts (`hC0`), the limit word of `tp` mapped and
unmapped under the frame condition (`hmr`, `hun`), `rS` in the pool, not
wrapping and off the callee's region given the caller's cells outside it
(`hsub`, `hfit`, `hFO`), and the overflow abort from the held-back abort
label (`hab`, at any saved `%rbp` and return address, under the
callee's frame conditions with the caller's cells outside it). -/
theorem userCallW_of_fn {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {fr : Scc.Emit.X64.Frame} {r : Res}
    {fn entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true) (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn cells fr entry 0 r.insts r.ret = true)
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isa} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hR8 : R.base.toNat % 8 = 0) (hZ8 : Z.toInt % 8 = 0)
    (hD : 8 + (fr.size : Int) ≤ D) (hD8 : D % 8 = 0)
    (hphB : bodyPhOk okPc ph (fun _ => false) lab cells fr entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts Λ lbl Spike.Lib.X64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m →
      StackOff rS (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) m)
    (hab : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base.toNat % 8 = 0 →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) → ∀ fp ra' : BitVec 64,
      SegW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms
        (Lag [d] (· = Spike.Lib.X64Consumer.c0) (At exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (abortN (immsOf d) (InWalk d) [d] lbl fr (_root_.Executable.labels exe).label fp ra'
            Spike.Lib.X64Consumer.c0)))
        (fun _ _ => False)) :
    UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D (Int64.ofInt fr.size)
      (UPost [d] lbl Spike.Lib.X64Consumer.c0) ra Spike.Lib.X64Consumer.c0 tp := by
  intro F' hR0 hF' hFF g hra hc htp
  -- the callee's region
  generalize hRc : R.callee (-8 - Z.toInt - 8 - 0) (-D) 8 = Rc at hR0 hF' hFF hFO hab ⊢
  have hlo : Rc.lo = -D := by rw [← hRc]; rfl
  have hhi : Rc.hi = 8 := by rw [← hRc]; rfl
  have hb8 : Rc.base.toNat % 8 = 0 := by
    rw [← hRc]; exact addr_toNat_mod8 R hR8 (by omega)
  have hrb8 : (rbR Rc).base.toNat % 8 = 0 := addr_toNat_mod8 Rc hb8 (by decide)
  have hrbOK : (rbR Rc).OK := rbR_ok hR0 (by omega) (by omega)
  have hFO' : ∀ m, F' m → StackOff rS Rc m := fun m h => hFO m (hFF m h).1 (hFF m h).2
  have hFOb : ∀ m, F' m → StackOff rS (rbR Rc) m :=
    fun m h => stackOff_rbR hR0 (by omega) (by omega) (hFO' m h)
  -- the source start
  have hfind : [d].find? (·.name == "main") = some d := by
    simp only [Scc.Lower.Accepted0, Bool.and_eq_true, beq_iff_eq] at hd
    simp [List.find?, hd.1.1.1.1.1.1]
  have hu : d.argTy = .unit := by
    simp only [Scc.Lower.Accepted0, Bool.and_eq_true, beq_iff_eq] at hd
    exact hd.1.1.1.2
  have hQ := quiet_c0 hd
  -- the entry's `%rsp` is the region's base
  refine SegW.mono_pre (P := fun s c => At exe endPc Rc F'
      (uN0 (_root_.Executable.labels exe).label ms F fn (Int64.ofInt fr.size) g) s c ∧ Rc.base = g.sp)
    (SegW.of_imp fun hbase => ?_) fun s c hAt => ⟨hAt, ?_⟩
  rotate_left
  · obtain ⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩ := hAt
    have := hA.so .rsp 0 (by simp [SO.get, uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  have hseg := fn0_seg (W := BodyW0 Λ μ own rS Tk lbl Spike.Lib.X64Consumer.c0) (K := K) (p := [d]) (lbl := lbl)
    (ms := ms) (J := (uN0 (_root_.Executable.labels exe).label ms F fn (Int64.ofInt fr.size) g).J)
    (fp := g.fp) (ra := g.ra) (c0 := Spike.Lib.X64Consumer.c0)
    hf h1 hI.lays hI.endOk hpro hr (fresh_unit d.arg) hbody (walk_immsOf d) hF' hR0 (by omega) (by omega)
    (proW_body0 hI h1 hpro hC0 (fun _ _ h => h.1.1.trans hc ▸ .refl _) hQ
      (fun _ _ h => h.1.2.2.2.2.trans htp) hphP hR0 hb8 (by omega) (by omega) (by omega) (by omega) hmr
      (fun m h => hun m (hFF m h).1) hsub hfit hFO')
    (hWb_of hI hf h1 hbody (hra ▸ hphB) hrbOK hrb8 (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) hsub hfit hFOb hC0 hQ)
    (hWs_of hI hf h1 hbody (hra ▸ hphB) hrbOK hrb8 (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) hsub hfit hFOb hC0 hQ)
    (fun σ c ⟨⟨hc0, hfp, hra0, hsp, htp0⟩, hlim⟩ => by
      have hc' : c = Spike.Lib.X64Consumer.c0 := hc0.trans hc
      subst hc'
      have hlim' := hlim.mono fun m h => (hFF m h).1
      have ha : σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec = limA g.tp := by
        rw [limA, htp0]; rfl
      rw [ha]
      refine ⟨⟨hlim'.rt, hlim'.mp, hlim'.unmapped, fun v hv => ?_⟩, hfp, hra0, fun _ => nj_start hfind hu, .refl _⟩
      rw [hsp]; exact hlim'.room v hv)
  have hlag := (bodyW0_lag hseg).mono_W (W' := fun s c => SFacts Λ μ own rS Tk lbl s c Dt)
    fun s c h => SFacts.dt_mono h fun _ h => h.elim
  refine (SegW.seq_left (Q := Lag [d] (· = Spike.Lib.X64Consumer.c0) (At exe endPc (rbR Rc) F'
      (abortN (immsOf d) (InWalk d) [d] lbl fr (_root_.Executable.labels exe).label g.fp g.ra
        Spike.Lib.X64Consumer.c0)))
    ((hlag.mono_pre fun s c hAt => by
        obtain ⟨-, -, -, -, σ, -, -, hJ, -⟩ := id hAt
        exact ⟨c, hAt, .refl c, hJ.1.trans hc⟩).mono_post fun s c h => by
      obtain ⟨c', hX, hr', hcc⟩ := h
      rcases hX with ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨a, t, w, hta, hho, hev, hnm, hv, hbp⟩, hr0⟩ | hX
      · have h' : At exe endPc (rbR Rc) F' ⟨Int64.ofBitVec g.ra, ⟨16, []⟩, fun σ (_ : Ctl) =>
            σ.regs.get64 .rbp = g.fp ∧ ValRep lbl w.val (σ.regs.get64 .rax).toNat⟩ s c :=
          ⟨he, hn, hdc, hpc, σ, hA, hD', hbp, hv⟩
        obtain ⟨he, hn, hdc, hpc, σ', hA', hD'', hbp', hv'⟩ :=
          at_of_rbR (J' := fun σ (_ : Ctl) => σ.regs.get64 .rbp = g.fp ∧ ValRep lbl w.val (σ.regs.get64 .rax).toNat)
            (fun _ _ h => h) h'
        have hsp := hA'.so .rsp (16 - 8) (by simp [SO.get])
        refine .inr ⟨he, hn, hdc, hpc, σ', hA', hD'', ⟨hcc, c', hcc ▸ hr0, a, t, w, hta, hho, hev, hnm, hv'⟩, hbp', ?_⟩
        rw [show σ'.regs.rsp.toBitVec = σ'.regs.get64 .rsp from rfl, hsp, Region.addr, hbase]
        rfl
      · exact .inl ⟨c', hX, hr', hcc⟩)
    (hab F' hR0 hb8 hF' hFF g.fp g.ra)).mono_post fun _ _ h => h.elim False.elim id

end Call

end Spike.Lib.LowerX64
