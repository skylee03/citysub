///|
priv struct CompletelyBounded {}

///|
fn Type::top_free(lhs : Type, ctx : Context) -> Bool {
  let ty = lhs.simplify(ctx)
  match ty {
    Top => false
    Var(_) => ty.promote?(ctx).unwrap().top_free(ctx)
    Arr(ty1, ty2) => ty1.top_free(ctx) && ty2.top_free(ctx)
    Record(ltys) => ltys.all(fn(lt) { lt.1.top_free(ctx) })
    Variant(ltys) => ltys.all(fn(lt) { lt.1.top_free(ctx) })
    All(x, ty1, ty2) =>
      ty1.top_free(ctx) && ty2.top_free(ctx.add_binding(x, TyVar(ty1)))
    _ => true
  }
}

///|
impl Subtyper for CompletelyBounded with subtype(self, lhs, rhs, ctx) -> Bool {
  if lhs.equiv(rhs, ctx) {
    match lhs {
      All(_, ty11, _) => ty11.top_free(ctx)
      _ => true
    }
  } else {
    let ty1 = lhs.simplify(ctx)
    let ty2 = rhs.simplify(ctx)
    match (ty1, ty2) {
      (_, Top) => true
      (Var(_), _) => self.subtype(ty1.promote?(ctx).unwrap(), ty2, ctx)
      (Arr(ty11, ty12), Arr(ty21, ty22)) =>
        self.subtype(ty21, ty11, ctx) && self.subtype(ty12, ty22, ctx)
      (Record(ltys1), Record(ltys2)) =>
        ltys2.all(fn(lt) {
          match ltys1.lookup(lt.0) {
            None => false
            Some(t1) => self.subtype(t1, lt.1, ctx)
          }
        })
      (Variant(ltys1), Variant(ltys2)) =>
        ltys1.all(fn(lt) {
          match ltys2.lookup(lt.0) {
            None => false
            Some(t2) => self.subtype(lt.1, t2, ctx)
          }
        })
      (All(x1, ty11, ty12), All(_, ty21, ty22)) if ty11.top_free(ctx) &&
        ty21.top_free(ctx) =>
        self.subtype(ty21, ty11, ctx) &&
        self.subtype(ty12, ty22, ctx.add_binding(x1, TyVar(ty21)))
      _ => false
    }
  }
}

///|
impl Subtyper for CompletelyBounded with join(self, lhs, rhs, ctx) -> Type {
  if self.subtype(lhs, rhs, ctx) {
    rhs
  } else if self.subtype(rhs, lhs, ctx) {
    lhs
  } else {
    let ty1 = lhs.simplify(ctx)
    let ty2 = lhs.simplify(ctx)
    match (ty1, ty2) {
      (Arr(ty11, ty12), Arr(ty21, ty22)) =>
        try {
          Arr(self.meet!(ty11, ty21, ctx), self.join(ty12, ty22, ctx))
        } catch {
          NoRuleApplies => Top
        }
      (Record(ltys1), Record(ltys2)) => {
        let labels1 = ltys1.map(fn(lty) { lty.0 })
        let labels2 = ltys2.map(fn(lty) { lty.0 })
        let common_labels = labels1.filter(fn(l) { labels2.contains(l) })
        let common_ltys = common_labels.map(fn(l) {
          let ty1 = ltys1.lookup(l).unwrap()
          let ty2 = ltys2.lookup(l).unwrap()
          (l, self.join(ty1, ty2, ctx))
        })
        Record(common_ltys)
      }
      (Variant(ltys1), Variant(ltys2)) => {
        let labels1 = ltys1.map(fn(lty) { lty.0 })
        let labels2 = ltys2.map(fn(lty) { lty.0 })
        let all_labels = labels1.concat(
          labels2.filter(fn(l) { not(labels1.contains(l)) }),
        )
        let all_ltys = loop (all_labels, @immut/list.Nil) {
          (Nil, acc) => break acc.rev()
          (Cons(l, rest), acc) => {
            let ty = match (ltys1.lookup(l), ltys2.lookup(l)) {
              (Some(ty1), Some(ty2)) => self.join(ty1, ty2, ctx)
              (Some(ty1), None) => ty1
              (None, Some(ty2)) => ty2
              (None, None) => panic()
            }
            continue (rest, Cons((l, ty), acc))
          }
        }
        Variant(all_ltys)
      }
      (All(x1, ty11, ty12), All(_, ty21, ty22)) =>
        try {
          if ty11.top_free(ctx) && ty21.top_free(ctx) {
            raise NoRuleApplies
          } else {
            let ty1 = self.meet!(ty11, ty21, ctx)
            All(x1, ty1, self.join(ty12, ty22, ctx.add_binding(x1, TyVar(ty1))))
          }
        } catch {
          NoRuleApplies => Top
        }
      _ => Top
    }
  }
}

///|
impl Subtyper for CompletelyBounded with meet(self, lhs, rhs, ctx) -> Type!NoRuleApplies {
  if self.subtype(lhs, rhs, ctx) {
    lhs
  } else if self.subtype(rhs, lhs, ctx) {
    rhs
  } else {
    let ty1 = lhs.simplify(ctx)
    let ty2 = lhs.simplify(ctx)
    match (ty1, ty2) {
      (Arr(ty11, ty12), Arr(ty21, ty22)) =>
        Arr(self.join(ty11, ty21, ctx), self.meet!(ty12, ty22, ctx))
      (Record(ltys1), Record(ltys2)) => {
        let labels1 = ltys1.map(fn(lty) { lty.0 })
        let labels2 = ltys2.map(fn(lty) { lty.0 })
        let all_labels = labels1.concat(
          labels2.filter(fn(l) { not(labels1.contains(l)) }),
        )
        let all_ltys = loop (all_labels, @immut/list.Nil) {
          (Nil, acc) => break acc.rev()
          (Cons(l, rest), acc) => {
            let ty = match (ltys1.lookup(l), ltys2.lookup(l)) {
              (Some(ty1), Some(ty2)) => self.meet!(ty1, ty2, ctx)
              (Some(ty1), None) => ty1
              (None, Some(ty2)) => ty2
              (None, None) => panic()
            }
            continue (rest, Cons((l, ty), acc))
          }
        }
        Record(all_ltys)
      }
      (Variant(ltys1), Variant(ltys2)) => {
        let labels1 = ltys1.map(fn(lty) { lty.0 })
        let labels2 = ltys2.map(fn(lty) { lty.0 })
        let common_labels = labels1.filter(fn(l) { labels2.contains(l) })
        let common_ltys = loop (common_labels, @immut/list.Nil) {
          (Nil, acc) => break acc.rev()
          (Cons(l, rest), acc) => {
            let ty1 = ltys1.lookup(l).unwrap()
            let ty2 = ltys2.lookup(l).unwrap()
            continue (rest, Cons((l, self.meet!(ty1, ty2, ctx)), acc))
          }
        }
        Variant(common_ltys)
      }
      (All(x1, ty11, ty12), All(_, ty21, ty22)) =>
        if ty11.top_free(ctx) && ty21.top_free(ctx) {
          raise NoRuleApplies
        } else {
          let ty1 = self.join(ty11, ty21, ctx)
          All(x1, ty1, self.meet!(ty12, ty22, ctx.add_binding(x1, TyVar(ty1))))
        }
      _ => raise NoRuleApplies
    }
  }
}
