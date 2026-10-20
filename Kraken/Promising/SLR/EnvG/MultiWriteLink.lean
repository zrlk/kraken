/-
Whole-thread environment (`EnvG`), phase 3: **the concrete link
for trees with several stores, by re-anchoring**. ISA-neutral.

Phase 1 relates the actual context of an instruction to `EnvG`'s by
`NodeRel` at the instruction's start configuration `c` (`LinkS.lean`);
phase 2 re-establishes it after every load (`MultiLink.lean`). After a
store, `NodeRel` at `c` is gone for good (the memory and the promises have
changed). This file **re-anchors** the next store at the intermediate
configuration

  `c₁ := c.withThread tid {t with prom := cx₁.prom, views := cx₁.views} cx₁.mem`

(the thread's views those of the context, so that `c₁` satisfies the machine
invariants: `Config.MachInv.withThread` from `Ctx.Inv` and the instruction's
own appends since `c`), with `NodeRel` at `c₁` for the context with its local
fields reset, and instruction views `ivAt iv n`, the views of the `n`-th
store (`InstrViews.forStore`, `dataPer` emptied so that store `0` of the new
anchor is store `n` of the instruction). The phase-1 store transport
`NodeRel.storeS` then answers the store from `c₁`; its outcome is carried
back to the actual context (`Ctx.SameVPM`: the write rules read only views,
promises and memory) and to the anchor `c` (`Erase.withThread_prom`,
`SnapLe.withThread_prom`, `RStep.monoB`, `WpPath.reanchor`).

The post relation after a write, `PostW`, is the phase-1 `PostS` at `c`, the
own appends since `c` (`OwnAppC`), and that the resource has no positive
write share the start resource lacks (`PosLe`: the path fact
`WpPath`'s written-permission conjunct asks it of every later store; stores
only give away, `posLe_store`).

**Scope**: no release in flight (`pf = none`), no load and no RMW after the
first store (`MultiWriteS` with `Rok := False`; trees ending in an RMW are
phase-2 trees, `MultiLink.lean`). A store may be a planned release (after
fences, `effRel`); the rule (`MultiWriteRule.lean`) rules out release-kind
stores (`NoRelWrite`) to keep prepay at phase-1 trees.

- `ivAt`, `Ctx.SameVPM` (+ `.write`, `.overtaken`, `.erAt`, `.rStep`),
  `CtxLe.transferW`, `CtxLe.ivChange`, `SnapLe.withThread_prom`,
  `RStep.monoB`, `WpPath.reanchor`, `posLe_store`;
- `OwnAppC`, `PosLe`, `PostW`, `PostS.r_eq`;
- `nodeSimW_envG`: the `NodeSimW` instance;
- `treeJ_envG_eraseWPRDW(_start)`: **link theorem 1** for trees with a store
  suffix, ending in the phase-1 `PostS` at the instruction's `cl`.
-/
import Kraken.Promising.SLR.EnvG.MultiLink
import Kraken.Promising.SLR.EnvG.MultiWriteTree

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The views of the `n`-th store -/

/-- The instruction views of store number `n` as the views of store `0`: its
own data views, `dataPer` emptied. -/
def ivAt (iv : InstrViews) (n : Nat) : InstrViews := { iv.forStore n with dataPer := [] }

theorem ivAt_forStore0 (iv : InstrViews) (n : Nat) : (ivAt iv n).forStore 0 = ivAt iv n := by
  simp [ivAt, InstrViews.forStore]

/-- The write rule reads only the scalar fields of the instruction views. -/
theorem writeSuccs_ivAt (A : Arch) (tid : Nat) (iv : InstrViews) (n : Nat) :
    writeSuccs A tid (ivAt iv n) = writeSuccs A tid (iv.forStore n) := rfl

theorem ivAt_le {iv : InstrViews} {m : Nat} (h : iv.Le m) (n : Nat) : (ivAt iv n).Le m :=
  have h' := h.forStore n
  ⟨h'.addrR, h'.addrW, h'.dataR, h'.dataW, h'.condW, fun _ hp => absurd hp List.not_mem_nil⟩

/-! ## Same views, promises and memory -/

/-- **Same views, promises and memory** (the local fields, `stores` and
`rmwWrote` included, free): what the write rule and `EraseWPRD`'s store
obligations read. -/
structure _root_.Kraken.Promising.Ctx.SameVPM (cx cy : Ctx) : Prop where
  views : cx.views = cy.views
  prom : cx.prom = cy.prom
  mem : cx.mem = cy.mem

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.Ctx.SameVPM

open Kraken.Promising.SLR

variable {A : Arch} {tid : Nat} {cx cy : Ctx}

theorem reset (cx : Ctx) : cx.SameVPM cx.reset := ⟨rfl, rfl, rfl⟩

theorem writeOk (h : cx.SameVPM cy) {ivs : InstrViews} {k : StoreKind} {l : Loc} {tr : Option Time} {extra : View}
    {t : Time} (hok : WriteOk A tid ivs cx k l tr extra t) : WriteOk A tid ivs cy k l tr extra t := by
  have hpre : writePre A ivs cx k extra = writePre A ivs cy k extra := by unfold writePre; rw [h.views]
  unfold WriteOk at hok ⊢
  rw [← hpre, ← h.views, ← h.mem]
  exact hok

theorem afterWrite (h : cx.SameVPM cy) {ivs : InstrViews} (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νfwd : View) (ful : Bool) :
    (Kraken.Promising.afterWrite A ivs cx k xcl l v t νfwd ful).SameVPM
      (Kraken.Promising.afterWrite A ivs cy k xcl l v t νfwd ful) :=
  ⟨by simp only [Kraken.Promising.afterWrite, h.views], by simp only [Kraken.Promising.afterWrite, h.prom],
    by simp only [Kraken.Promising.afterWrite, h.mem]⟩

/-- **The write correspondence** (`Ctx.Same.write` without `stores` and
`rmwWrote`). -/
theorem write (h : cx.SameVPM cy) {ivs : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {cx' : Ctx} (hc : cx' ∈ writeSuccs A tid ivs cx k xcl l v tr extra) :
    ∃ cy' ∈ writeSuccs A tid ivs cy k xcl l v tr extra, cx'.SameVPM cy' := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, ht, w, hw, hl, hv, htid, hok, rfl⟩ | ⟨hok, rfl⟩
  · exact ⟨_, (mem_writeSuccs A tid).mpr (.inl ⟨t, h.prom ▸ ht, w, h.mem ▸ hw, hl, hv, htid, h.writeOk hok, rfl⟩),
      h.afterWrite _ _ _ _ _ _ _⟩
  · refine ⟨_, (mem_writeSuccs A tid).mpr (.inr ⟨by rw [← h.mem]; exact h.writeOk hok, rfl⟩), ?_⟩
    have h' : ({ cx with
        mem := (cx.mem.append { loc := l, val := v, tid }).1
        prom := cx.prom ++ [cx.mem.last + 1]
        promisedNow := cx.promisedNow ++
          [({ loc := l, val := v, tid }, max (writePre A ivs cx k extra) (cx.views.getCoh l))] } : Ctx).SameVPM
        { cy with
          mem := (cy.mem.append { loc := l, val := v, tid }).1
          prom := cy.prom ++ [cy.mem.last + 1]
          promisedNow := cy.promisedNow ++
            [({ loc := l, val := v, tid }, max (writePre A ivs cy k extra) (cy.views.getCoh l))] } :=
      ⟨h.views, by simp only [h.prom, h.mem], by simp only [h.mem]⟩
    rw [h.mem] at h' ⊢
    exact h'.afterWrite _ _ _ _ _ _ _

theorem overtaken (h : cx.SameVPM cy) (ho : cy.Overtaken) : cx.Overtaken := by
  obtain ⟨p, hp, w, hw, hle⟩ := ho
  exact ⟨p, h.prom ▸ hp, w, h.mem ▸ hw, h.views ▸ hle⟩

theorem erAt (h : cx.SameVPM cy) {I : ISA} {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I}
    {r : Res} {g : Ghost} (he : ErAt rF T c t tid r g cy) : ErAt rF T c t tid r g cx := by
  unfold ErAt at he ⊢; rw [h.prom, h.mem]; exact he

theorem rStep (h : cx.SameVPM cy) {B : Time} {r r' : Res} {g g' : Ghost} (hr : RStep B r g r' g' cy) :
    RStep B r g r' g' cx := by
  unfold RStep at hr ⊢; rw [h.views]; exact hr

end Kraken.Promising.Ctx.SameVPM

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-! ## Transfers -/

/-- The environment context `cxe` with all its local fields re-chosen for the
actual context `cx`. -/
def envLocalsW (cxe cx : Ctx) : Ctx :=
  { cxe with loadViews := cx.loadViews.map fun _ => 0, succView := 0, stores := cx.stores, rmwWrote := cx.rmwWrote }

theorem envLocalsW_views (cxe cx : Ctx) : (envLocalsW cxe cx).views = cxe.views := rfl

/-- **`CtxLe` transfers to a `SameVPM` context** (bounded), the
environment's local fields re-chosen (`CtxLe.transfer` with `stores` and
`rmwWrote` free). -/
theorem CtxLe.transferW {iv : InstrViews} {cx cy cxe : Ctx} (h : CtxLe iv cy cxe) (hs : cx.SameVPM cy)
    (hb : cx.Bnd) : CtxLe iv cx (envLocalsW cxe cx) := by
  obtain ⟨⟨⟨r1, r2, r3, -, -, -, -⟩, -, hpd, hda, hivr, hivb, hnle, hfgn⟩, hme, hpe⟩ := h
  have hl : Rel2 (fun a' a => a' ≤ (TMap.idUpTo cx.mem.last).fv a) (cx.loadViews.map fun _ => (0 : View))
      cx.loadViews := by
    generalize cx.loadViews = ls
    induction ls with
    | nil => exact .nil
    | cons a ls ih => exact .cons (Nat.zero_le _) ih
  refine ⟨⟨⟨?_, ?_, ?_, hl, Nat.zero_le _, rfl, rfl⟩, hb, ?_, ?_, by rw [hs.mem]; exact hivr, ?_, Nat.zero_le _, ?_⟩,
    ?_, ?_⟩
  · show MemRel _ cx.mem cxe.mem; rw [hs.mem]; exact r1
  · show ViewsLe _ cxe.views cx.views; rw [hs.views, hs.mem]; exact r2
  · show PromRel _ cx.prom cxe.prom; rw [hs.prom, hs.mem]; exact r3
  · rw [hs.prom, hs.mem]; exact hpd
  · rw [hs.mem]; exact hda
  · rw [hs.mem]; exact hivb
  · show FgnSep _ cxe.mem _ _; rw [hs.mem]; exact hfgn
  · show cxe.mem = cx.mem; rw [hs.mem]; exact hme
  · show cxe.prom = cx.prom; rw [hs.prom]; exact hpe

/-- `CtxLe` at other instruction views bounded by the memory. -/
theorem CtxLe.ivChange {iv iv' : InstrViews} {cx cxe : Ctx} (h : CtxLe iv cx cxe) (hb : iv'.Le cx.mem.last) :
    CtxLe iv' cx cxe := by
  obtain ⟨⟨hrel, hbnd, hpd, hda, -, -, hnle, hfgn⟩, hme, hpe⟩ := h
  exact ⟨⟨hrel, hbnd, hpd, hda, ivLe_envIv _ iv', hb, hnle, hfgn⟩, hme, hpe⟩

/-- `SnapLe` reads only the promise list of the thread. -/
theorem SnapLe.withThread_prom {tid : Nat} {s c : Config I} {t₁ t₂ : Thread I} {m : Memory}
    (h : SnapLe tid s (c.withThread tid t₁ m)) (hn : tid < c.threads.size) (hp : t₂.prom = t₁.prom) :
    SnapLe tid s (c.withThread tid t₂ m) := by
  refine ⟨h.init, h.msgs, fun t ht => ?_⟩
  obtain ⟨t', ht', ps, hps, hlt⟩ := h.prom t ht
  rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl] at ht'
  cases ht'
  exact ⟨t₂, by rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl], ps, hp.trans hps, hlt⟩

/-- `RStep` at a smaller bound. -/
theorem RStep.monoB {B B' : Time} {r r' : Res} {g g' : Ghost} {cx : Ctx} (h : RStep B' r g r' g' cx) (hB : B ≤ B') :
    RStep B r g r' g' cx :=
  ⟨fun b hb => h.1 b (Nat.le_trans hb hB), fun b hb => h.2 b (Nat.le_trans hb hB)⟩

/-! ## Positive write shares -/

/-- **No new positive write share**: every location `r` may write to, `rS`
may. -/
def PosLe (rS r : Res) : Prop := ∀ x, 0 < (r.wr x).q → 0 < (rS.wr x).q

theorem PosLe.refl (r : Res) : PosLe r r := fun _ h => h

theorem PosLe.trans {r₁ r₂ r₃ : Res} (h₁ : PosLe r₁ r₂) (h₂ : PosLe r₂ r₃) : PosLe r₁ r₃ :=
  fun x h => h₁ x (h₂ x h)

/-- **A store gives away, never gains**: the virtual resource after a
permitted store has no positive write share the one before lacks (a planned
release keeps `Plan.keep`, which with what it gives is the old resource). -/
theorem posLe_store {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {l : Loc} {v : Val}
    (hok : StoreOk A tid pl σ k false l v) (hout : StoreOut A tid pl σ σ' k false l v true) : PosLe σ.r σ'.r := by
  obtain ⟨-, -, -, -, tw, -, -, -, -, -, -, -, ⟨P, -, hr⟩, -⟩ := hout
  intro x hx
  rw [hr] at hx
  unfold Plan.after at hx
  cases hrl : pl.rel l v with
  | false => simpa [hrl] using hx
  | true =>
    simp only [hrl, ↓reduceIte, Res.addW_q] at hx
    have hgl := (hok.2.2.2 hrl).2.2.1
    have e := congrArg (fun ρ => (ρ.wr x).q) (pl.keep_op_give hgl P σ.r (v, tw))
    simp only [Res.op, Perm.op, Res.addW_q] at e
    have := ((pl.give l v P σ.r).wr x).nonneg
    grind

/-! ## Path facts across a re-anchor -/

/-- **`WpPath` across a re-anchor**: from the start `(c, t)` to `cx₁`, then
from the re-anchor `c₁` (thread `t₁` with `cx₁`'s promises, `c`'s other
threads) to `cx₂`, given that the second write did not add promises and
kept `cx₁`'s memory, and that its resource gains no write share. -/
theorem WpPath.reanchor {tid : Nat} {c c₁ : Config I} {t t₁ : Thread I} {rS r₁ r₂ : Res} {gS g₁ g₂ : Ghost}
    {cx₁ cx₂ : Ctx} (h₁ : WpPath c tid t rS gS r₁ g₁ cx₁) (h₂ : WpPath c₁ tid t₁ r₁ g₁ r₂ g₂ cx₂)
    (hoth : ∀ i, i ≠ tid → c₁.threads[i]? = c.threads[i]?) (hp₁ : t₁.prom = cx₁.prom) (hm₁ : c₁.mem = cx₁.mem)
    (hprom : ∀ p ∈ cx₂.prom, p ∈ cx₁.prom) (hpre : ∀ ts, ts ≤ cx₁.mem.last → cx₂.mem.get? ts = cx₁.mem.get? ts)
    (hpos : PosLe rS r₁) : WpPath c tid t rS gS r₂ g₂ cx₂ := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5⟩ := h₂
  refine ⟨a1.trans b1, fun ts hts ho => ?_, fun ts h => a3 ts (b3 ts h), fun x h => a4 x (b4 x h), fun w hw => ?_⟩
  · have h1 : ts ∈ g₁.pend := by
      refine a2 ts hts ?_
      rcases ho with ho | ho
      · exact .inl (hprom ts ho)
      · exact .inr ho
    refine b2 ts h1 ?_
    rcases ho with ho | ⟨i, t', hne, hi, ho⟩
    · exact .inl ho
    · exact .inr ⟨i, t', hne, by rw [hoth i hne]; exact hi, ho⟩
  · obtain ⟨ts, hget, hnp, hnew⟩ := hw
    by_cases hw2 : cx₁.mem.last < ts ∨ ts ∈ t₁.prom
    · exact hpos _ (b5 w ⟨ts, hget, hnp, by rw [hm₁]; exact hw2⟩)
    · simp only [not_or] at hw2
      obtain ⟨hle, hnp1⟩ := hw2
      refine a5 w ⟨ts, ?_, hp₁ ▸ hnp1, hnew⟩
      rw [← hpre ts (Nat.le_of_not_lt hle)]; exact hget

/-! ## The post relation after a write -/

section Rel

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **The instruction's own appends since `c`**: `c`'s memory is a prefix of
the context's, and every message above it is the thread's. -/
def OwnAppC (tid : Nat) (m : Memory) (cx : Ctx) : Prop :=
  Ctx.OwnApp tid ({ views := cx.views, prom := cx.prom, mem := m } : Ctx) cx

theorem OwnAppC.of_mem {tid : Nat} {m : Memory} {cx : Ctx} (h : cx.mem = m) : OwnAppC tid m cx :=
  Ctx.OwnApp.of_mem h

theorem OwnAppC.trans {tid : Nat} {m : Memory} {cx cx' : Ctx} (h : OwnAppC tid m cx) (h' : cx.OwnApp tid cx') :
    OwnAppC tid m cx' :=
  ⟨h.pre.trans h'.pre, (Ctx.OwnApp.trans (c' := cx) ⟨h.pre, h.tid⟩ h').tid⟩

/-- **After a write** (phase 3): the phase-1 `PostS` at the start knowledge
`cl₀ ∧ ClAt tid rv₀ g₀ c` without a release in flight, the own appends since
`c`, and no write share the start resource lacks. -/
def PostW (tid : Nat) (pl : Plan) (iv : InstrViews) (c : Config I) (t : Thread I) (rv₀ : Res) (g₀ : Ghost)
    (cl₀ : Prop) (rS : Res) (gS : Ghost) (σ : State I) (r : Res) (g : Ghost) (cx : Ctx) : Prop :=
  PostS tid pl iv c t rv₀ g₀ (cl₀ ∧ ClAt tid rv₀ g₀ c) none rS gS σ r g cx ∧ OwnAppC tid c.mem cx ∧ PosLe rS r

/-- With no own pending promise after the access, the actual resource is the
env's. -/
theorem PostS.r_eq {cl : Prop} {pf : Option (Loc × Val)} {rS : Res} {gS : Ghost} {σ : State I} {r : Res}
    {g : Ghost} {cx : Ctx} (h : PostS tid pl iv c t rv₀ g₀ cl pf rS gS σ r g cx) : r = σ.r := by
  rcases h.1.res with ⟨e, -⟩ | ⟨ts, -, -, h1, h2, -⟩
  · exact e
  · exact absurd h2 (h.2.2.2.1 ts h1)

end Rel

/-! ## The transport -/

section Link

variable {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
  {rv₀ : Res} {g₀ : Ghost} {cl₀ : Prop}

/-- **A store after a write**, re-anchored at the intermediate
configuration. -/
theorem PostW.store {rS : Res} {gS : Ghost} (ht : c.threads[tid]? = some t) (hmc : c.MachInv)
    {k : StoreKind} {l : Loc} {v : Val} {σ₁ : State I} {r₁ : Res} {g₁ : Ghost} {cx₁ : Ctx}
    (hp : PostW tid pl iv c t rv₀ g₀ cl₀ rS gS σ₁ r₁ g₁ cx₁) (hok : StoreOk A tid pl σ₁ k false l v) {cx₂ : Ctx}
    (hc : cx₂ ∈ writeSuccs A tid (iv.forStore cx₁.stores) cx₁ k false l v none)
    (E : ErAt rF (fun _ => True) c t tid r₁ g₁ cx₁) (hi : cx₁.Inv tid) (hm : c.mem.last ≤ cx₁.mem.last) :
    cx₂.Overtaken ∨ ∃ r₂ g₂ σ₂, StoreOut A tid pl σ₁ σ₂ k false l v true ∧
      ErAt rF (fun _ => True) c t tid r₂ g₂ cx₂ ∧ RStep c.mem.last r₁ g₁ r₂ g₂ cx₂ ∧
      PostW tid pl iv c t rv₀ g₀ cl₀ rS gS σ₂ r₂ g₂ cx₂ := by
  obtain ⟨⟨hpr, hwp, hlast, hnpd, -⟩, hown, hpos⟩ := hp
  have hn := lt_size_of_get? ht
  obtain ⟨cxe, hce, hve⟩ := hpr.ctx
  have hb1 : cx₁.Bnd := hce.sim.bnd
  have hivb : iv.Le cx₁.mem.last := hce.sim.ivb
  -- the re-anchor
  let ivs := ivAt iv cx₁.stores
  let t₁ : Thread I := { t with prom := cx₁.prom, views := cx₁.views }
  let c₁ : Config I := c.withThread tid t₁ cx₁.mem
  have ht₁ : c₁.threads[tid]? = some t₁ := by
    show (c.withThread tid t₁ cx₁.mem).threads[tid]? = _
    rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl]
  have hmc₁ : c₁.MachInv := hmc.withThread hn ⟨hi.prom, hi.nodup, hi.own⟩ hown.pre hown.tid
  have hE₁ : Erase (setRes rF tid r₁) g₁ (fun _ => True) c₁ := Erase.withThread_prom E hn rfl
  have hN : NodeRel tid pl ivs rF c₁ t₁ σ₁.r g₁ σ₁.cl σ₁ r₁ g₁ cx₁.reset := {
      ht := ht₁
      mach := hmc₁
      mem := rfl
      prom := rfl
      erase := hE₁
      g0 := rfl
      rv := rfl
      snap := SnapLe.withThread_prom hpr.snap hn rfl
      ghost := hpr.ghost
      ctx := by
        refine (hce.reset.congrT (cxe' := envCtx tid σ₁.vs c₁) ?_ ?_ ?_ rfl rfl rfl rfl).ivChange (ivAt_le hivb _)
        · exact hve.symm
        · show ownProm tid c₁ = cxe.prom; rw [ownProm_eq ht₁, hce.prom]
        · show c₁.mem = cxe.mem; rw [hce.mem]; rfl
      res := hpr.res
      cl := id
      fenced := hpr.fenced }
  have hst : StartS tid c₁ t₁ g₁ none := ⟨fun _ ts hts => hnpd ts hts, fun _ _ e => absurd e (by simp)⟩
  -- the store from the reset context
  have hcI : cx₂ ∈ writeSuccs A tid ivs cx₁ k false l v none := hc
  obtain ⟨cy₂, hcy, hS⟩ := (Ctx.SameVPM.reset cx₁).write hcI
  have hcy' : cy₂ ∈ writeSuccs A tid (ivs.forStore cx₁.reset.stores) cx₁.reset k false l v none := by
    rw [Ctx.reset_stores, ivAt_forStore0]; exact hcy
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi
  have hown₂ := (writeSuccs_inv A tid _ hc hi).2
  obtain ⟨hb2, hl12⟩ := writeSuccs_bnd A tid _ hb1 (hivb.forStore _) (Nat.zero_le _) hc
  rcases hN.storeS hst (.inl rfl) hok hcy' ⟨hi.prom, hi.nodup, hi.own⟩ with
    ho | ⟨r₂, g₂, σ₂, hout, E', hR, hpr', hwp', -, hpd', hcl'⟩
  · exact .inl (hS.overtaken ho)
  have ewt : ∀ p : List Time, c₁.withThread tid { t₁ with prom := p } cy₂.mem =
      c.withThread tid { t with prom := p, views := cx₁.views } cx₂.mem := by
    intro p; show (c.withThread tid t₁ cx₁.mem).withThread tid _ _ = _
    rw [Config.withThread_withThread, hS.mem]
  have hr₁ : r₁ = σ₁.r := PostS.r_eq ⟨hpr, hwp, hlast, hnpd, fun h => absurd rfl h⟩
  have hr₂ : r₂ = σ₂.r := by
    rcases hpr'.res with ⟨e, -⟩ | ⟨ts, -, -, h1, h2, -⟩
    · exact e
    · exact absurd h2 (hpd' ts h1)
  have hpos₂ : PosLe rS r₂ := hr₂ ▸ hpos.trans (hr₁ ▸ posLe_store hok hout)
  refine .inr ⟨r₂, g₂, σ₂, hout, ?_, RStep.monoB (hS.rStep hR) hm, ⟨⟨⟨?_, hpr'.ghost, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    fun h => absurd rfl h⟩, hown.trans hown₂, hpos₂⟩⟩
  · -- erasure at the anchor `c`
    unfold ErAt at E' ⊢
    rw [ewt] at E'
    rw [hS.prom]
    exact Erase.withThread_prom E' hn rfl
  · -- the snapshot
    have := hpr'.snap
    rw [ewt] at this
    rw [hS.prom]
    exact SnapLe.withThread_prom this hn rfl
  · -- the context
    obtain ⟨cye, hcye, hvye⟩ := hpr'.ctx
    exact ⟨_, (hcye.transferW hS hb2).ivChange (hivb.mono hl12), hvye⟩
  · rw [hS.prom, hS.mem]; exact hpr'.res
  · intro h0; rw [hcl']; exact hpr.cl h0
  · rw [hS.views]; exact hpr'.fenced
  · -- the path facts
    refine WpPath.reanchor hwp (hwp'.congr hS.mem hS.prom) (fun i hne => ?_) rfl rfl ?_ ?_ hpos
    · show (c.withThread tid t₁ cx₁.mem).threads[i]? = _
      rw [Config.withThread_get? c _ _ hn, ite_eq_right (Ne.symm hne)]
    · intro p hp'; rw [hev.prom] at hp'; exact List.mem_of_mem_erase hp'
    · intro ts hts
      rcases hev.cases with ⟨hm', -⟩ | ⟨hm', -⟩
      · rw [hm']
      · rw [hm', Memory.get?_append_of_le _ _ _ hts]
  · exact Nat.le_trans hm hl12
  · intro ts hts; rw [← hS.prom] at hpd'; exact hpd' ts hts


theorem OwnAppC.congr {m : Memory} {cx cx' : Ctx} (h : OwnAppC tid m cx) (hm : cx'.mem = cx.mem) :
    OwnAppC tid m cx' :=
  ⟨by rw [hm]; exact h.pre, fun ts w hts hw => h.tid ts w hts (by rw [← hm]; exact hw)⟩

/-- **The per-node transport of `EnvG` for trees with a store suffix** (no
release in flight, no RMW: `Rok := False`). -/
theorem nodeSimW_envG {rS : Res} {gS : Ghost} (ht : c.threads[tid]? = some t) (hmc : c.MachInv)
    (hst : StartS tid c t gS none) :
    NodeSimW A tid iv rF (fun _ => True) c t (EnvG I A tid pl) (LokS none) (SokS none) (fun _ => False) (LokS none)
      (fun σ r g cx => PreM tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx)
      (fun σ r g cx => PostW tid pl iv c t rv₀ g₀ cl₀ rS gS σ r g cx) := by
  have H := nodeSimM_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀) (cl₀ := cl₀)
    (rS := rS) hst
  have hrS : ∀ {σ r g cx}, PreM tid pl iv rF c t rv₀ g₀ cl₀ rS gS σ r g cx → r = rS ∧ rS = σ.r ∧ cx.mem = c.mem :=
    fun {σ r g cx} hpre => by
      obtain ⟨⟨hN, rfl, rfl⟩, -⟩ := hpre
      refine ⟨rfl, ?_, hN.mem⟩
      rcases hN.res with ⟨e, -⟩ | ⟨ts, -, -, h1, h2, -⟩
      · exact e
      · exact absurd h2 (hst.none rfl ts h1)
  exact {
  pre_post := fun hd hpre => by
    obtain ⟨rfl, -, hm⟩ := hrS hpre
    exact ⟨H.pre_post hd hpre, OwnAppC.of_mem hm, PosLe.refl _⟩
  fence_pre := H.fence_pre
  fence_post := by
    rintro k σ r g cx ⟨hp, ho, hq⟩ hok
    obtain ⟨σ', hst', hp'⟩ := H.fence_post hp hok
    exact ⟨σ', hst', hp', ho.congr (fenceStep_mem cx k), hq⟩
  load := H.load
  store := by
    rintro k xcl addr n v σ r g cx hS hpre hok
    obtain rfl : xcl = false := hok.1
    refine ⟨fun cx' hc E hi hm => ?_, fun hx => absurd hx Bool.false_ne_true⟩
    obtain ⟨rfl, hrσ, hmem⟩ := hrS hpre
    rcases (H.store hS hpre hok).1 cx' hc E hi hm with ho | ⟨r', g', σ', hst', E', hR, hp'⟩
    · exact .inl ho
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc
      refine .inr ⟨r', g', σ', hst', E', hR, hp', (OwnAppC.of_mem hmem).trans (writeSuccs_inv A tid _ hc hi).2, ?_⟩
      rw [PostS.r_eq hp', hrσ]
      exact posLe_store hok hst'
  rmw := by
    intro k addr n op σ r g cx h
    exact h.elim
  store_post := by
    rintro k xcl addr n v σ r g cx - hp hok
    obtain rfl : xcl = false := hok.1
    refine ⟨fun cx' hc E hi hm => ?_, fun hx => absurd hx Bool.false_ne_true⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    exact PostW.store ht hmc hp hok hc E hi hm }

/-- **Link theorem 1 for `EnvG`, trees with a store suffix**: from the
phase-1 node relation at the instruction's start (no local field written
yet), the erasure WP with the phase-1 post relation at the start knowledge
`cl₀`. -/
theorem treeJ_envG_eraseWPRDW {rS : Res} {gS : Ghost} (ht : c.threads[tid]? = some t) (hmc : c.MachInv)
    (hst : StartS tid c t gS none) {σT : Type} {Q : σT → State I → Prop} {tree : EvTree σT} {σ : State I}
    (hW : (TreeJLive.eraseWPRDW (nodeSimW_envG (A := A) (pl := pl) (iv := iv) (rF := rF) (rv₀ := rv₀) (g₀ := g₀)
      (cl₀ := cl₀) (rS := rS) ht hmc hst) Q).W tree σ)
    {cx : Ctx} (h : NodeRel tid pl iv rF c t rv₀ g₀ cl₀ σ rS gS cx) (hs : cx.stores = 0) (hw : cx.rmwWrote = false)
    (ha : MultiWriteS (LokS none) (SokS none) (fun _ => False) (LokS none) tree) :
    tree.EraseWPRD A tid iv rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl iv c t rv₀ g₀ cl₀ none rS gS σ' r' g' cx')) rS gS cx := by
  have hN : NodeRel tid pl iv rF c t rv₀ g₀ (cl₀ ∧ ClAt tid rv₀ g₀ c) σ rS gS cx.reset :=
    { h.toReset (Ctx.Same.refl cx) with cl := fun h0 => h.cl h0.1 }
  refine EvTree.EraseWPRD.mono (fun _ _ _ _ ⟨s, hq, hp⟩ => ⟨s, hq, hp.1.of_clM⟩) tree _ _ _
    (treeJ_eraseWPRDW _ hW ⟨⟨hN, rfl, rfl⟩, hs, hw, h.ctx.sim.bnd⟩ ha)

/-- **Link theorem 1 at an instruction's start, trees with a store suffix**:
from `EnvRel` and the hypotheses of `ThreadRuleRX.wp`, at `ctx₀`, without a
release in flight. -/
theorem treeJ_envG_eraseWPRDW_start {σ : State I} {r : Res} {g : Ghost} {cl : Prop}
    (hrel : EnvRel tid pl σ c t r g cl) (d : InstrDeps I.RegId) (hst : StartS tid c t g none)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) {σT : Type}
    {Q : σT → State I → Prop} {tree : EvTree σT}
    (hW : (TreeJLive.eraseWPRDW (nodeSimW_envG (A := A) (pl := pl) (iv := instrViews t d) (rF := rF) (rv₀ := σ.r)
      (g₀ := g) (cl₀ := cl) (rS := r) hrel.ht hm hst) Q).W tree σ)
    (ha : MultiWriteS (LokS none) (SokS none) (fun _ => False) (LokS none) tree) :
    tree.EraseWPRD A tid (instrViews t d) rF (fun _ => True) c t
      (PostOf (E := EnvG I A tid pl) Q
        (fun (σ' : State I) r' g' cx' => PostS tid pl (instrViews t d) c t σ.r g cl none r g σ' r' g' cx')) r g
      (ctx₀ t tid c.mem) :=
  treeJ_envG_eraseWPRDW hrel.ht hm hst hW (hrel.toNodeRel rF d E hm) rfl rfl ha

end Link

end Kraken.Promising.SLR.EnvG
