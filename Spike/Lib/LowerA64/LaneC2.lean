/-
**A lane store's premise** (AArch64): `LaneC` (`Body2.lean`) from
`lane_segW` (`Spike/Lib/LowerA64/LaneSeg.lean`), the source's exchange site
(`Spike/Lib/Src/XchgSiteB.lean`) and `NJB.xchg2`; the twin of the x86-64
`Spike/Lib/LowerX64/LaneC2.lean`.

- `insts_xchg`: the two instructions' code;
- `group_elem2`, `ofEnv2_elem2`: an `elem2` binding's placement;
- `opdVal_upd_fresh`: `x%n`'s slot off the environment's operands;
- `laneJ`, `laneP`: the lane's node and source relation at the exchange;
- `LaneH`: the site's facts `laneC_of` gives `LaneW`'s discharge;
- `laneC_of`: `LaneC` from `LaneW`, the memory side's reads
  numbers and `LblRoom`.
-/
import Spike.Lib.LowerA64.LaneSeg
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.NJBXchg2
import Spike.Lib.Src.XchgSiteB
import Spike.Lib.Src.LblRange

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (xchgLoad xchgStore)
open Spike.Lib.Form (opdVal SEnv group grp WordPl NodeJ NodeJE)
open Scc.Lower.Inv (atomV regName)
open Scc.Lower (elem2)

/-! ## The code -/

/-- **A lane store's two instructions' code**: each instruction's items
and code block, back to back, up to `pc'`. -/
theorem insts_xchg {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop} {kk : Nat}
    {pc pc' : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {w : Scc.IR.Operand}
    (h : InstsC2 cx Cd Bl kk pc [xchgLoad d a, xchgStore a w] pc') :
    ∃ l1 l2, cx.inst kk (xchgLoad d a) = .ok l1 ∧ Cd pc (directives l1) ∧
      cx.inst (kk + 1) (xchgStore a w) = .ok l2 ∧ Cd (pc + Int64.ofNat (4 * (directives l1).length)) (directives l2) ∧
      pc' = pc + Int64.ofNat (4 * ((directives l1).length + (directives l2).length)) := by
  rcases h with ⟨-, l1, hl1, hc1, h⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  · rcases h with ⟨-, l2, hl2, hc2, rfl⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
    · refine ⟨l1, l2, hl1, hc1, hl2, hc2, ?_⟩
      rw [Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
    all_goals first | cases he | simp [xchgStore, Spike.Lib.LowerShape.newBufCall] at he
  all_goals first | cases he | simp [xchgLoad, Spike.Lib.LowerShape.newBufCall] at he

/-! ## The new binding -/

/-- **An `elem2` type groups one operand as one word.** -/
theorem group_elem2 {u : Ty} (hu : elem2 u = true) (w : Scc.IR.Operand) : group u [w] = some [.one w] := by
  cases u <;> simp_all [elem2, group, grp]

theorem ofEnv2_elem2 (env : Scc.Lower.Env) (x : String) {u : Ty} (hu : elem2 u = true) (d : Scc.IR.Reg) :
    ofEnv2 ((x, u, [.reg d]) :: env) = (x, u, [.one (.reg d)]) :: ofEnv2 env := by
  simp [ofEnv2, group_elem2 hu]

/-- **An operand off `d` keeps its value** when `d`'s slot is updated. -/
theorem opdVal_upd_fresh {cx : FnCtx} {d : Scc.IR.Reg} {k : Int} (hd : rsOf cx d = some k) {o : Scc.IR.Operand}
    (ho : ∀ r, o = .reg r → r ≠ d) (sl : Int → BitVec 64) (v : BitVec 64) :
    opdVal (rsOf cx) (upd sl k v) o = opdVal (rsOf cx) sl o :=
  Spike.Lib.Form.opdVal_upd fun r k' hor hr => by
    have hk : k' ≠ k := fun hk => ho r hor (rsOf_inj hr (hk ▸ hd))
    simp [upd, hk]

theorem slotAddr_base (ob : Scc.ObjLayout) (b : Scc.IR.Reg) (w : UInt64) (s : Bool × Nat) :
    (Spike.Lib.LowerShape.slotAddr ob b w s).base = b := by
  obtain ⟨tr, i⟩ := s
  cases tr <;> rfl

theorem refO_mem {bw : List Scc.IR.Operand} {q o : Scc.IR.Operand} (h : Spike.Lib.LowerShape.refO bw = some (q, o)) :
    q ∈ bw := by
  match bw, h with
  | [_], h => simp only [Spike.Lib.LowerShape.refO, Option.some.injEq, Prod.mk.injEq] at h; simp [h.1]
  | [_, _], h => simp only [Spike.Lib.LowerShape.refO, Option.some.injEq, Prod.mk.injEq] at h; simp [h.1]

/-! ## The premise -/

section Lane

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- The lane's node at the exchange: `bodyN2` at the term `t`, the thread
pointer `tp` (`laneC_of`'s `J`). -/
def laneJ (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat) (cx : FnCtx)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (pc : Int64) (t : Expr) (env : Scc.Lower.Env)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) : AS → Ctl → Prop :=
  ((bodyN2 p lbl lsize i cx fp ra c0 pc t (ofEnv2 env) lits cs bufs).withTp tp).J

/-- The lane's source relation at the exchange: the local run to `c1`
reaches `NodeJ` at `t` with the environment's literal, buffer and size
facts (`laneC_of`'s `P`). -/
def laneP (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cx : FnCtx) (t : Expr)
    (env : Scc.Lower.Env)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) : AS → Ctl → Ctl → Prop :=
  fun σ c c1 => LocalRun p c c1 ∧ ∃ L sm B, NodeJE lbl (rsOf cx) t (ofEnv2 env) σ.slot c1 ∧ EnvLit lits c1.env ∧
    EnvB lits cs bufs L sm lsize c1.env ∧ MemB L sm B ∧ EnvSmall c1.env

/-- **The lane's facts at the exchange site** for `LaneW`'s discharge
(`laneC_of` proves them): at each state `σ`, control `c` of `J` and site
control `c1` of `P`, `c1` at the `let` `t` (not a `ret`); given the walk's facts at `t`
(free variables placed, register bases, immediates), `c1` placed in the slot
file, also with `d`'s slot updated; the base's value not moved by `d`'s
slot; and the element's word `vb + disp` the `k`-th word of a placed label
`l` at `b`, `k < lsize l`. -/
def LaneH (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat) (cx : FnCtx) (t : Expr) (env : Scc.Lower.Env)
    (d : Scc.IR.Reg) (a : Scc.IR.Addr) (J : AS → Ctl → Prop) (P : AS → Ctl → Ctl → Prop) : Prop :=
  ∀ σ c c1, J σ c → P σ c c1 →
    c1.term = t ∧ (∀ a, c1.term ≠ .ret a) ∧
    ((∀ y ∈ Scc.Sem.exprFv t, (Spike.Lib.Form.lookupS (ofEnv2 env) y).isSome) → LocBaseRegAt (ofEnv2 env) t →
      ImmIn i (ofEnv2 env) t →
      SlotRepAt i lbl (rsOf cx) σ.slot c1 ∧
        ∀ k, rsOf cx d = some k → ∀ v, SlotRepAt i lbl (rsOf cx) (upd σ.slot k v) c1) ∧
    (∀ k, rsOf cx d = some k → ∀ r, opdVal (rsOf cx) (upd σ.slot k r) (.reg a.base) =
      opdVal (rsOf cx) σ.slot (.reg a.base)) ∧
    ∀ vb : BitVec 64, opdVal (rsOf cx) σ.slot (.reg a.base) = some vb.toNat →
      ∃ l b k, lbl l = some b ∧ k < lsize l ∧ (vb + BitVec.ofInt 64 a.disp).toNat = b + 8 * k

/-- **A lane store's premise** (`LaneC`) from `lane_segW`: the memory
side's states at the lane's nodes in `W₀` (`LaneW` at `laneJ`, `laneP`), the
memory side's reads numbers
(`hrd`), the labels with room for a displacement (`LblRoom`), every placed
label's words in the heap or `.data` (`hrg`), none of which the frame
condition's private memory loads (`hwn`); the source's
site from `xchg_site`, `xchg_val`, past it `NJB.xchg2`. -/
theorem laneC_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hrd : ∀ w', (ms fs).rd w' → IsNum w')
    (hroom : LblRoom lbl) {Λ : Scc.Sem.Layout} (hrg : LblRange Λ lbl lsize)
    (hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone Λ m.dmem) {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    {Ab : FragS isaLSE2} (lcx : Scc.Lower.Ctx) (tp : UInt64)
    (hLW : ∀ (c0 : Ctl) (pc : Int64) (t : Expr) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (d : Scc.IR.Reg) (a : Scc.IR.Addr) (w : Scc.IR.Operand), G0 c0 → T t →
      (∀ y ∈ Scc.Sem.exprFv t, (Spike.Lib.Form.lookupS (ofEnv2 env) y).isSome) → LocBaseRegAt (ofEnv2 env) t →
      ImmIn i (ofEnv2 env) t →
      LaneH lbl lsize i cx t env d a (laneJ p lbl lsize i cx fp ra tp c0 pc t env lits cs bufs)
        (laneP p lbl lsize cx t env lits cs bufs) →
      LaneW Cd W₀ K exe endPc R F (ms fs) lbl cx pc d a w (laneJ p lbl lsize i cx fp ra tp c0 pc t env lits cs bufs)
        (laneP p lbl lsize cx t env lits cs bufs)) :
    LaneC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk env n x b j v e t bw rb o tj iv μ u nu mu tv w s1 lits cs bufs hG0 hT hfr _ _ hg _ hX hb hrf hj
    he hro hv hs hi htot' himm' hlb' htot himm hlb
  obtain ⟨l1, l2, hl1, hc1, hl2, hc2, rfl⟩ := insts_xchg hi
  obtain ⟨-, ls, -, hsr, -⟩ := inst_xchgLoad_inv hl1
  cases hso : cx.slotOff (regName x n) with
  | error => simp [FnCtx.setReg, hso, bind, Except.bind] at hsr
  | ok off =>
  have hdk : rsOf cx (regName x n) = some (off - cx.frame) := by simp [rsOf, hso]
  have hrbf : ∀ r', Scc.IR.Operand.reg (Spike.Lib.LowerShape.slotAddr lcx.obj rb
      (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1).base = .reg r' → r' ≠ regName x n := by
    rw [slotAddr_base]; intro r' h; cases h
    exact atomV_fresh hfr hb x _ (refO_mem hrf) rb rfl
  -- the site's facts for `LaneW`
  have hH : LaneH lbl lsize i cx (.let_ x (.xchgAt b j v) e) env (regName x n)
      (Spike.Lib.LowerShape.slotAddr lcx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1)
      (laneJ p lbl lsize i cx fp ra tp c0 pc (.let_ x (.xchgAt b j v) e) env lits cs bufs)
      (laneP p lbl lsize cx (.let_ x (.xchgAt b j v) e) env lits cs bufs) := by
    intro σ c c1 _ ⟨_, L, sm, B, hj', _, hbE, _, _⟩
    obtain ⟨-, sa, vb, k, -, -, hvb, hdisp, hk28, -, hlv, hks, hlt, -⟩ :=
      xchg_site hj' hbE hX hg hroom hb hrf hj he hro hs lcx.obj
    refine ⟨hj'.1, (fun _ h => by rw [hj'.1] at h; cases h),
      fun htot hlb himm => ⟨SlotRepAt.of_nodeJE hj' htot hlb himm, fun k' hk' v' => ?_⟩,
      fun k' hk' r => opdVal_upd_fresh hk' hrbf σ.slot r, fun vb' hvb' => ?_⟩
    · have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
          opdVal (rsOf cx) (upd σ.slot k' v') o' = opdVal (rsOf cx) σ.slot o' :=
        fun q hq pl hpl o' ho' => Spike.Lib.Form.opdVal_upd fun r' k'' hor hr' => by
          have hk : k'' ≠ k' := fun hk =>
            fresh_ofEnv2 hfr x q hq pl hpl o' ho' r' hor (rsOf_inj hr' (hk ▸ hk'))
          simp [upd, hk]
      exact SlotRepAt.of_nodeJE ⟨hj'.1, hj'.2.1, hj'.2.2.congr hsl'⟩ htot hlb himm
    · have hvv : vb'.toNat = vb := by
        rw [slotAddr_base] at hvb'; exact (Option.some.inj (hvb'.symm.trans hvb))
      exact ⟨_, _, _, hlv, hks, by rw [hdisp, toNat_add_ofInt8 (by omega), hvv]⟩
  have h0 := lane_segW (lbl := lbl) (ms := ms fs) hf h1 h16 hF hR hal hlo hhi hso hl1 hl2 hCd hc1
    hc2
    (J := laneJ p lbl lsize i cx fp ra tp c0 pc (.let_ x (.xchgAt b j v) e) env lits cs bufs)
    (J' := fun σ c => ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
      ((bodyN2 p lbl lsize i cx fp ra c0' (pc + Int64.ofNat (4 * ((directives l1).length + (directives l2).length))) e
        (ofEnv2 ((x, u, [.reg (regName x n)]) :: env)) ((x, Scc.Lower.opLit lcx.prog lits (.xchgAt b j v)) :: lits)
        (Scc.Lower.csAfter x cs (.xchgAt b j v)) (Scc.Lower.bufsAfter x cs bufs (.xchgAt b j v))).withTp tp).J σ c)
    (P := laneP p lbl lsize cx (.let_ x (.xchgAt b j v) e) env lits cs bufs)
    (fun σ c ⟨⟨⟨L, sm, B, c', hr, hj', hn, hbE, hm, hS⟩, _, _, _⟩, _⟩ => ⟨c', hr, hr, L, sm, B, hj', hn, hbE, hm, hS⟩)
    (fun σ c c1 ⟨⟨_, hfj, hc0, _⟩, htp⟩ ⟨hr, L, sm, B, hj', hn, hbE, hm, hS⟩ => by
      obtain ⟨hu, sa, vb, k, hsite, hh, hvb, hdisp, -, -, hlv, hks, hlt, hrep⟩ :=
        xchg_site hj' hbE hX hg hroom hb hrf hj he hro hs lcx.obj
      refine ⟨x, sa, u, v, e, hsite, hh, fun vb' hvb' => ?_⟩
      have hvv : vb'.toNat = vb := by
        rw [slotAddr_base] at hvb'; exact (Option.some.inj (hvb'.symm.trans hvb))
      have hadd : (vb' + BitVec.ofInt 64 (Spike.Lib.LowerShape.slotAddr lcx.obj rb
          (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1).disp).toNat = vb + 8 * k := by
        rw [hdisp, toNat_add_ofInt8 (by omega), hvv]
      refine ⟨by rw [hadd]; exact hrep, fun m hm => heapWord_none hrg (hwn m hm) hlv hks hadd,
        fun r w' hrdw hrw => ?_⟩
      refine ⟨by rw [opdVal_upd_fresh hdk hrbf]; exact hvb', fun vw hvw => ?_⟩
      rw [opdVal_upd_fresh hdk (atomV_fresh hfr hv x w (List.mem_singleton_self _))] at hvw
      obtain ⟨tv', wv, nv, hev, hnv, hV⟩ := xchg_val hj' hg hv
      have hnn : nv = vw.toNat := Option.some.inj (hnv.symm.trans hvw)
      have hfr' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds, ∀ r' k', o' = .reg r' → rsOf cx r' = some k' →
          k' ≠ off - cx.frame := fun q hq pl hpl o' ho r' k' hor hrk hk =>
        fresh_ofEnv2 hfr x q hq pl hpl o' ho r' hor (rsOf_inj hrk (hk ▸ hdk))
      refine ⟨⟨tv', wv, hev, hnn ▸ hV⟩, fun σ2 hsl2 htp2 => ?_⟩
      refine ⟨⟨e, (x, u, [w']) :: c1.env, none⟩,
        (FrameRunM.ofLocal (hc0.trans hr) fs).trans (FrameRunM.mem1 hh hj'.1 trivial), ⟨⟨?_, ?_, .refl _, ?_⟩, ?_⟩⟩
      · rw [hsl2, ofEnv2_elem2 env x hu]
        exact ⟨L, sm, B, NJB.xchg2 hj' hn hbE hm hS hu (hrd w' hrdw) hdk hfr' hrw⟩
      · obtain ⟨h0', h8', hle'⟩ := slotOff_bounds hf hso
        have hk1 : (-16 : Int) ≠ off - cx.frame := by omega
        have hk2 : (-8 : Int) ≠ off - cx.frame := by omega
        rw [hsl2]; simp only [FrJ, upd, hk1, hk2, ↓reduceIte]; exact hfj
      · rw [hsl2]
        refine SlotRepAt.of_nodeJE (NodeJE.xchg2 (u := u) hj' hdk hfr' hrw) ?_ ?_ ?_
        · rw [← ofEnv2_elem2 env x hu]; exact htot'
        · rw [← ofEnv2_elem2 env x hu]; exact hlb'
        · rw [← ofEnv2_elem2 env x hu]; exact himm'
      · exact htp2.trans htp)
    (hLW c0 pc _ env lits cs bufs _ _ _ hG0 hT htot hlb himm hH)
  refine (SegWS.liftS fs h0 hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => ?_
  obtain ⟨he', hn', hdd, hpc, σ, hA, hFm, c0', hrun, hJ⟩ := h
  exact .inl ⟨hfs, c0', hrun, he', hn', hdd, hpc, σ, hA, hFm, hJ⟩

end Lane

end Spike.Lib.LowerA64
