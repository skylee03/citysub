///|
pub(all) enum Type {
  Bool
  Arr(Type, Type)
  Var(Int, Int)
  Id(String)
  Unit
  Record(@immut/list.T[(String, Type)])
  Variant(@immut/list.T[(String, Type)])
  String
  All(String, Type, Type)
  Top
}

///|
fn Type::map(self : Type, onvar : (Int, Int, Int) -> Type, c : Int) -> Type {
  match self {
    Arr(ty1, ty2) => Arr(ty1.map(onvar, c), ty2.map(onvar, c))
    Var(x, n) => onvar(c, x, n)
    Record(ltys) => Record(ltys.map(fn(lty) { (lty.0, lty.1.map(onvar, c)) }))
    Variant(ltys) => Variant(ltys.map(fn(lty) { (lty.0, lty.1.map(onvar, c)) }))
    All(x, ty1, ty2) => All(x, ty1.map(onvar, c), ty2.map(onvar, c + 1))
    _ => self
  }
}

///|
fn Type::shift_above(self : Type, d : Int, c : Int) -> Type {
  self.map(
    fn(c, x, n) { if x >= c { Var(x + d, n + d) } else { Var(x, n + d) } },
    c,
  )
}

///|
fn Type::shift(self : Type, d : Int) -> Type {
  self.shift_above(d, 0)
}

///|
fn Type::subst(self : Type, j : Int, s : Type) -> Type {
  self.map(fn(c, x, n) { if x == j + c { s.shift(c) } else { Var(x, n) } }, 0)
}

///|
fn Type::subst_top(self : Type, s : Type) -> Type {
  self.subst(0, s.shift(1)).shift(-1)
}

///|
fn Type::to_string(self : Type, ctx : Context) -> String {
  let logger = StringBuilder::new()
  self.output(ctx, true, logger)
  logger.to_string()
}

///|
fn Type::output(
  self : Type,
  ctx : Context,
  outer : Bool,
  logger : &Logger
) -> Unit {
  match self {
    Bool => logger.write_string("Bool")
    Arr(ty1, ty2) => {
      ty1.output(ctx, outer, logger)
      if outer {
        logger.write_string(" ")
      }
      logger.write_string("->")
      if outer {
        logger.write_string(" ")
      }
      ty2.output(ctx, outer, logger)
    }
    Var(x, _) => logger.write_string(ctx.index_to_name(x))
    Id(b) => logger.write_string(b)
    Unit => logger.write_string("Unit")
    Record(ltys) => {
      logger.write_string("{")
      loop (ltys, 1) {
        (Nil, _) => break
        (Cons((l, ty), rest), i) => {
          if i > 1 {
            logger.write_string(",")
            if outer {
              logger.write_string(" ")
            }
          }
          if l != i.to_string() {
            logger.write_string("\{l}:")
          }
          ty.output(ctx, false, logger)
          continue (rest, i + 1)
        }
      }
      logger.write_string("}")
    }
    Variant(ltys) => {
      logger.write_string("<")
      loop (ltys, 1) {
        (Nil, _) => break
        (Cons((l, ty), rest), i) => {
          if i > 1 {
            logger.write_string(",")
            if outer {
              logger.write_string(" ")
            }
          }
          if l != i.to_string() {
            logger.write_string("\{l}:")
          }
          ty.output(ctx, false, logger)
          continue (rest, i + 1)
        }
      }
      logger.write_string(">")
    }
    String => logger.write_string("String")
    All(x, ty1, ty2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("All \{x1}")
      logger.write_string(" <: ")
      ty1.output(ctx, false, logger)
      logger.write_string(". ")
      ty2.output(ctx1, outer, logger)
    }
    Top => logger.write_string("Top")
  }
}

///|
fn Type::promote(self : Type, ctx : Context) -> Type!NoRuleApplies {
  match self {
    Var(x, _) =>
      match ctx.get_binding(x) {
        TyVar(ty) => ty
        _ => raise NoRuleApplies
      }
    _ => raise NoRuleApplies
  }
}

///|
fn Type::lcst(self : Type, ctx : Context) -> Type {
  let ty = self.simplify(ctx)
  try {
    ty.promote!(ctx).lcst(ctx)
  } catch {
    NoRuleApplies => ty
  }
}

///|
fn Type::compute(self : Type, ctx : Context) -> Type!NoRuleApplies {
  match self {
    Bool
    | Arr(_)
    | Id(_)
    | Unit
    | Record(_)
    | Variant(_)
    | String
    | All(_)
    | Top => raise NoRuleApplies
    Var(x, _) =>
      match ctx.get_binding(x) {
        TyAbb(ty) => ty
        TyVar(_) => raise NoRuleApplies
        _ => panic()
      }
  }
}

///|
fn Type::simplify(self : Type, ctx : Context) -> Type {
  loop self {
    ty =>
      try {
        continue ty.compute!(ctx)
      } catch {
        NoRuleApplies => break ty
      }
  }
}

///|
fn Type::equiv(self : Type, other : Type, ctx : Context) -> Bool {
  let ty1 = self.simplify(ctx)
  let ty2 = other.simplify(ctx)
  match (ty1, ty2) {
    (Bool, Bool) | (Unit, Unit) | (String, String) | (Top, Top) => true
    (Arr(ty11, ty12), Arr(ty21, ty22)) =>
      ty21.equiv(ty11, ctx) && ty12.equiv(ty22, ctx)
    (Var(x1, _), Var(x2, _)) => x1 == x2
    (Id(b1), Id(b2)) => b1 == b2
    (Record(ltys1), Record(ltys2)) =>
      ltys1
      .zip(ltys2)
      .map_or(false, fn(l) {
        l.all(fn(p) { p.0.0 == p.1.0 && p.0.1.equiv(p.1.1, ctx) })
      })
    (Variant(ltys1), Variant(ltys2)) =>
      ltys1
      .zip(ltys2)
      .map_or(false, fn(l) {
        l.all(fn(p) { p.0.0 == p.1.0 && p.0.1.equiv(p.1.1, ctx) })
      })
    (All(x1, ty11, ty12), All(_, ty21, ty22)) => {
      let ctx1 = ctx.add_binding(x1, TyVar(ty21))
      ty21.equiv(ty11, ctx) && ty12.equiv(ty22, ctx1)
    }
    _ => false
  }
}

///|
fn Type::subtype(self : Type, other : Type, ctx : Context) -> Bool {
  subtyper.val.subtype(self, other, ctx)
}

///|
fn Type::join(self : Type, other : Type, ctx : Context) -> Type {
  subtyper.val.join(self, other, ctx)
}

///|
fn Type::meet(self : Type, other : Type, ctx : Context) -> Type!NoRuleApplies {
  subtyper.val.meet!(self, other, ctx)
}
