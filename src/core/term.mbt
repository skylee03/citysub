///|
pub(all) enum Term {
  True(@info.Info)
  False(@info.Info)
  If(@info.Info, Term, Term, Term)
  Var(@info.Info, Int, Int)
  Abs(@info.Info, String, Type, Term)
  App(@info.Info, Term, Term)
  Unit(@info.Info)
  Ascribe(@info.Info, Term, Type)
  Record(@info.Info, @immut/list.T[(String, Term)])
  Proj(@info.Info, Term, String)
  Tag(@info.Info, String, Term, Type)
  Case(@info.Info, Term, @immut/list.T[(String, (String, Term))])
  String(@info.Info, String)
  TAbs(@info.Info, String, Type, Term)
  TApp(@info.Info, Term, Type)
  Concat(@info.Info, Term, Term)
}

///|
fn Term::map(
  self : Term,
  onvar : (@info.Info, Int, Int, Int) -> Term,
  ontype : (Int, Type) -> Type,
  c : Int
) -> Term {
  match self {
    True(info) => True(info)
    False(info) => False(info)
    If(info, t1, t2, t3) =>
      If(
        info,
        t1.map(onvar, ontype, c),
        t2.map(onvar, ontype, c),
        t3.map(onvar, ontype, c),
      )
    Var(info, x, n) => onvar(info, c, x, n)
    Abs(info, x, ty1, t2) =>
      Abs(info, x, ontype(c, ty1), t2.map(onvar, ontype, c + 1))
    App(info, t1, t2) =>
      App(info, t1.map(onvar, ontype, c), t2.map(onvar, ontype, c))
    Unit(info) => Unit(info)
    Ascribe(info, t1, ty1) =>
      Ascribe(info, t1.map(onvar, ontype, c), ontype(c, ty1))
    Record(info, lts) =>
      Record(info, lts.map(fn(lt) { (lt.0, lt.1.map(onvar, ontype, c)) }))
    Proj(info, t1, l) => Proj(info, t1.map(onvar, ontype, c), l)
    Tag(info, l, t1, ty) =>
      Tag(info, l, t1.map(onvar, ontype, c), ontype(c, ty))
    Case(info, t1, cases) =>
      Case(
        info,
        t1.map(onvar, ontype, c),
        cases.map(fn(case) {
          (case.0, (case.1.0, case.1.1.map(onvar, ontype, c + 1)))
        }),
      )
    String(info, s) => String(info, s)
    TAbs(info, x, ty1, t2) =>
      TAbs(info, x, ontype(c, ty1), t2.map(onvar, ontype, c + 1))
    TApp(info, t1, ty2) => TApp(info, t1.map(onvar, ontype, c), ontype(c, ty2))
    Concat(info, t1, t2) =>
      Concat(info, t1.map(onvar, ontype, c), t2.map(onvar, ontype, c))
  }
}

///|
fn Term::shift_above(self : Term, d : Int, c : Int) -> Term {
  self.map(
    fn(info, c, x, n) {
      if x >= c {
        Var(info, x + d, n + d)
      } else {
        Var(info, x, n + d)
      }
    },
    fn(c, ty) { ty.shift_above(d, c) },
    c,
  )
}

///|
fn Term::shift(self : Term, d : Int) -> Term {
  self.shift_above(d, 0)
}

///|
fn Term::subst(self : Term, j : Int, s : Term) -> Term {
  self.map(
    fn(info, c, x, n) { if x == j + c { s.shift(c) } else { Var(info, x, n) } },
    fn(_, ty) { ty },
    0,
  )
}

///|
fn Term::subst_top(self : Term, s : Term) -> Term {
  self.subst(0, s.shift(1)).shift(-1)
}

///|
fn Term::subst_ty(self : Term, j : Int, s : Type) -> Term {
  self.map(
    fn(info, _, x, n) { Var(info, x, n) },
    fn(c, ty) { ty.subst(j + c, s) },
    0,
  )
}

///|
fn Term::subst_ty_top(self : Term, s : Type) -> Term {
  self.subst_ty(0, s.shift(1)).shift(-1)
}

///|
fn Term::to_string(self : Term, ctx : Context) -> String {
  let logger = StringBuilder::new()
  self.output(ctx, logger)
  logger.to_string()
}

///|
fn Term::output(self : Term, ctx : Context, logger : &Logger) -> Unit {
  match self {
    True(_) => logger.write_string("true")
    False(_) => logger.write_string("false")
    If(_, t1, t2, t3) => {
      logger.write_string("if ")
      t1.output(ctx, logger)
      logger.write_string(" then ")
      t2.output(ctx, logger)
      logger.write_string(" else ")
      t3.output(ctx, logger)
    }
    Var(_, x, _) => logger.write_string(ctx.index_to_name(x))
    Abs(_, x, ty1, t2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("fn \{x1} : ")
      ty1.output(ctx, false, logger)
      logger.write_string(". ")
      t2.output(ctx1, logger)
    }
    App(_, t1, t2) => {
      t1.output(ctx, logger)
      logger.write_string(" ")
      t2.output(ctx, logger)
    }
    Unit(_) => logger.write_string("()")
    Ascribe(_, t1, ty1) => {
      t1.output(ctx, logger)
      logger.write_string(" as ")
      ty1.output(ctx, false, logger)
    }
    Record(_, lts) => {
      logger.write_string("{")
      loop (lts, 1) {
        (Nil, _) => break
        (Cons((l, t), rest), i) => {
          if i > 1 {
            logger.write_string(", ")
          }
          logger.write_string("\{l}=")
          t.output(ctx, logger)
          continue (rest, i + 1)
        }
      }
      logger.write_string("}")
    }
    Proj(_, t1, l) => {
      t1.output(ctx, logger)
      logger.write_string(".\{l}")
    }
    Tag(_, l, t1, ty) => {
      logger.write_string("<\{l}=")
      t1.output(ctx, logger)
      logger.write_string("> as ")
      ty.output(ctx, false, logger)
    }
    Case(_, t1, cases) => {
      logger.write_string("case ")
      t1.output(ctx, logger)
      logger.write_string(" of ")
      loop (cases, 1) {
        (Nil, _) => break
        (Cons((l, (x, t)), rest), i) => {
          if i > 1 {
            logger.write_string(" | ")
          }
          let (ctx1, x1) = ctx.pick_fresh_name(x)
          logger.write_string("<\{l} = \{x1}> => ")
          t.output(ctx1, logger)
          continue (rest, i + 1)
        }
      }
    }
    String(_, s) => logger.write_string("\"\{s}\"")
    TAbs(_, x, ty1, t2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("fn \{x1} <: ")
      ty1.output(ctx, false, logger)
      logger.write_string(". ")
      t2.output(ctx1, logger)
    }
    TApp(_, t1, ty2) => {
      t1.output(ctx, logger)
      logger.write_string(" [")
      ty2.output(ctx, false, logger)
      logger.write_string("]")
    }
    Concat(_, t1, t2) => {
      t1.output(ctx, logger)
      logger.write_string(" + ")
      t2.output(ctx, logger)
    }
  }
}

///|
fn is_val(self : Term) -> Bool {
  match self {
    True(_) | False(_) | Abs(_) | Unit(_) | String(_) | TAbs(_) => true
    Record(_, lts) => lts.all(fn(lt) { lt.1.is_val() })
    Tag(_, _, t1, _) => t1.is_val()
    _ => false
  }
}

///|
fn eval_rec(self : Term, ctx : Context) -> Term!NoRuleApplies {
  match self {
    True(_) | False(_) | Abs(_) | Unit(_) | String(_) | TAbs(_) =>
      raise NoRuleApplies
    If(info, t1, t2, t3) =>
      if t1.is_val() {
        match t1 {
          True(_) => t2
          False(_) => t3
          _ => raise NoRuleApplies
        }
      } else {
        If(info, t1.eval_rec!(ctx), t2, t3)
      }
    Var(_, x, _) =>
      match ctx.get_binding(x) {
        TmAbb(t, _) => t
        _ => raise NoRuleApplies
      }
    App(info, t1, t2) =>
      if t1.is_val() {
        if t2.is_val() {
          match t1 {
            Abs(_, _, _, t12) => t12.subst_top(t2)
            _ => raise NoRuleApplies
          }
        } else {
          App(info, t1, t2.eval_rec!(ctx))
        }
      } else {
        App(info, t1.eval_rec!(ctx), t2)
      }
    Ascribe(info, t1, ty1) =>
      if t1.is_val() {
        t1
      } else {
        Ascribe(info, t1.eval_rec!(ctx), ty1)
      }
    Record(info, lts) =>
      loop (lts, @immut/list.Nil) {
        (Nil, _) => raise NoRuleApplies
        (Cons((l, t), rest), acc) =>
          if t.is_val() {
            continue (rest, Cons((l, t), acc))
          } else {
            break Record(
              info,
              acc.rev_concat(Cons((l, t.eval_rec!(ctx)), rest)),
            )
          }
      }
    Proj(info, t1, l) =>
      if t1.is_val() {
        match t1 {
          Record(_, lts) =>
            match lts.lookup(l) {
              None => raise NoRuleApplies
              Some(t) => t
            }
          _ => raise NoRuleApplies
        }
      } else {
        Proj(info, t1.eval_rec!(ctx), l)
      }
    Tag(info, l, t1, ty) =>
      if t1.is_val() {
        raise NoRuleApplies
      } else {
        Tag(info, l, t1.eval_rec!(ctx), ty)
      }
    Case(info, t1, cases) =>
      if t1.is_val() {
        match t1 {
          Tag(_, l, t11, _) =>
            match cases.lookup(l) {
              None => raise NoRuleApplies
              Some((_, t)) => t.subst_top(t11)
            }
          _ => raise NoRuleApplies
        }
      } else {
        Case(info, t1.eval_rec!(ctx), cases)
      }
    TApp(info, t1, ty2) =>
      if t1.is_val() {
        match t1 {
          TAbs(_, _, _, t12) => t12.subst_ty_top(ty2)
          _ => raise NoRuleApplies
        }
      } else {
        TApp(info, t1.eval_rec!(ctx), ty2)
      }
    Concat(info, t1, t2) =>
      if t1.is_val() {
        if t2.is_val() {
          match (t1, t2) {
            (String(_, s1), String(_, s2)) => String(info, s1 + s2)
            _ => raise NoRuleApplies
          }
        } else {
          Concat(info, t1, t2.eval_rec!(ctx))
        }
      } else {
        Concat(info, t1.eval_rec!(ctx), t2)
      }
  }
}

///|
fn eval(self : Term, ctx : Context) -> Term {
  loop self {
    t =>
      try {
        continue t.eval_rec!(ctx)
      } catch {
        NoRuleApplies => break t
      }
  }
}

///|
fn derive_type!(self : Term, ctx : Context) -> Type {
  match self {
    True(_) | False(_) => Bool
    If(info, t1, t2, t3) =>
      if t1.derive_type!(ctx).subtype(Bool, ctx) {
        let ty2 = t2.derive_type!(ctx)
        let ty3 = t3.derive_type!(ctx)
        ty2.join(ty3, ctx)
      } else {
        @info.error_info!("guard of conditional is not a boolean", info~)
      }
    Var(_, x, _) => ctx.get_type(x)
    Abs(_, x, ty1, t2) => {
      let ctx1 = ctx.add_binding(x, Var(ty1))
      let ty2 = t2.derive_type!(ctx1).shift(-1)
      Arr(ty1, ty2)
    }
    App(info, t1, t2) => {
      let ty1 = t1.derive_type!(ctx)
      let ty2 = t2.derive_type!(ctx)
      match ty1.lcst(ctx) {
        Arr(ty11, ty12) =>
          if ty2.subtype(ty11, ctx) {
            ty12
          } else {
            @info.error_info!("parameter type mismatch", info~)
          }
        _ => @info.error_info!("arrow type expected", info~)
      }
    }
    Unit(_) => Unit
    Ascribe(info, t1, ty2) =>
      if t1.derive_type!(ctx).subtype(ty2, ctx) {
        ty2
      } else {
        @info.error_info!(
          "body of as-term does not have the expected type",
          info~,
        )
      }
    Record(info, lts) =>
      loop (lts, @immut/list.Nil) {
        (Nil, acc) => break Record(acc.rev())
        (Cons((l, t), rest), acc) =>
          if acc.lookup(l).is_empty() {
            continue (rest, Cons((l, t.derive_type!(ctx)), acc))
          } else {
            @info.error_info!("duplicate label \{l} is not allowed", info~)
          }
      }
    Proj(info, t1, l) =>
      match t1.derive_type!(ctx).lcst(ctx) {
        Record(ltys) =>
          match ltys.lookup(l) {
            None => @info.error_info!("label \{l} not found", info~)
            Some(ty) => ty
          }
        _ => @info.error_info!("record type expected", info~)
      }
    Tag(info, l, t1, ty) =>
      match ty.lcst(ctx) {
        Variant(ltys) =>
          match ltys.lookup(l) {
            None => @info.error_info!("label \{l} not found", info~)
            Some(ann_ty) =>
              if t1.derive_type!(ctx).subtype(ann_ty, ctx) {
                ty
              } else {
                @info.error_info!(
                  "variant does not have the expected type",
                  info~,
                )
              }
          }
        _ => @info.error_info!("annotation is not a variant type", info~)
      }
    Case(info, t1, cases) =>
      match t1.derive_type!(ctx).lcst(ctx) {
        Variant(ltys) => {
          for case in cases {
            if ltys.lookup(case.0).is_empty() {
              @info.error_info!("label \{case.0} not in type", info~)
            }
          }
          let case_tys = loop (cases, @immut/list.Nil) {
            (Nil, acc) => break acc.rev()
            (Cons((l, (x, t)), rest), acc) => {
              let ty = ltys.lookup(l).unwrap()
              let ctx1 = ctx.add_binding(x, Var(ty))
              continue (rest, Cons(t.derive_type!(ctx1).shift(-1), acc))
            }
          }
          let ty1 = case_tys.unsafe_head()
          case_tys.fold(init=ty1, fn(ty1, ty2) { ty1.join(ty2, ctx) })
        }
        _ => @info.error_info!("variant type expected", info~)
      }
    String(_) => String
    TAbs(_, x, ty1, t2) => {
      let ctx1 = ctx.add_binding(x, TyVar(ty1))
      let ty2 = t2.derive_type!(ctx1)
      All(x, ty1, ty2)
    }
    TApp(info, t1, ty2) => {
      let ty1 = t1.derive_type!(ctx)
      match ty1.lcst(ctx) {
        All(_, ty11, ty12) =>
          if not(ty2.subtype(ty11, ctx)) {
            @info.error_info!("type parameter bound mismatch", info~)
          } else {
            ty12.subst_top(ty2)
          }
        _ => @info.error_info!("universal type expected", info~)
      }
    }
    Concat(info, t1, t2) =>
      if t1.derive_type!(ctx).subtype(String, ctx) &&
        t2.derive_type!(ctx).subtype(String, ctx) {
        String
      } else {
        @info.error_info!("argument of concat is not a string", info~)
      }
  }
}
