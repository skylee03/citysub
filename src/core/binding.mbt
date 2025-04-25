///|
pub(all) enum Binding {
  Name
  TmAbb(Term, Type?)
  Var(Type)
  TyAbb(Type)
  TyVar(Type)
}

///|
fn Binding::shift(self : Binding, d : Int) -> Binding {
  match self {
    Name => Name
    TmAbb(t, ty_opt) => TmAbb(t.shift(d), ty_opt.map(fn(ty) { ty.shift(d) }))
    Var(ty) => Var(ty.shift(d))
    TyAbb(ty) => TyAbb(ty.shift(d))
    TyVar(ty) => TyVar(ty.shift(d))
  }
}

///|
fn Binding::to_string(self : Binding, ctx : Context) -> String {
  match self {
    Name => "/"
    TmAbb(t, Some(ty)) => "= \{t.to_string(ctx)}\n  : \{ty.to_string(ctx)}"
    Var(ty) => ": \{ty.to_string(ctx)}"
    TyAbb(ty) => "= \{ty.to_string(ctx)}"
    TyVar(ty) => "<: \{ty.to_string(ctx)}"
    _ => panic()
  }
}

///|
fn Binding::eval(self : Binding, ctx : Context) -> Binding {
  match self {
    TmAbb(t, ty_opt) => TmAbb(t.eval(ctx), ty_opt)
    _ => self
  }
}

///|
fn Binding::derive_type!(
  self : Binding,
  ctx : Context,
  info : @info.Info
) -> Binding {
  match self {
    TmAbb(t, None) => TmAbb(t, Some(t.derive_type!(ctx)))
    TmAbb(t, Some(ty)) =>
      if t.derive_type!(ctx).subtype(ty, ctx) {
        TmAbb(t, Some(ty))
      } else {
        @info.error_info!("type of binding does not match declared type", info~)
      }
    _ => self
  }
}
