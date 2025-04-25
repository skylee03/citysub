///|
type Context @immut/list.T[(String, Binding)]

///|
pub fn Context::empty() -> Context {
  Nil
}

///|
pub fn Context::length(self : Context) -> Int {
  self._.length()
}

///|
pub fn Context::add_binding(
  self : Context,
  x : String,
  bind : Binding
) -> Context {
  Cons((x, bind), self._)
}

///|
pub fn Context::add_name(self : Context, x : String) -> Context {
  self.add_binding(x, Name)
}

///|
pub fn Context::name_to_index!(
  self : Context,
  x : String,
  info : @info.Info
) -> Int {
  loop (0, self._) {
    (_, Nil) => @info.error_info!("identifier \"\{x}\" is unbound", info~)
    (i, Cons((y, _), rest)) => if y == x { i } else { continue (i + 1, rest) }
  }
}

///|
fn Context::index_to_name(self : Context, x : Int) -> String {
  self._.unsafe_nth(x).0
}

///|
pub fn Context::is_name_bound(self : Context, x : String) -> Bool {
  self._.any(fn(b) { x == b.0 })
}

///|
fn Context::pick_fresh_name(self : Context, x : String) -> (Context, String) {
  loop x {
    x =>
      if self.is_name_bound(x) {
        continue x + "'"
      } else {
        break (self.add_name(x), x)
      }
  }
}

///|
fn Context::get_binding(self : Context, x : Int) -> Binding {
  self._.unsafe_nth(x).1.shift(x + 1)
}

///|
fn Context::get_type(self : Context, x : Int) -> Type {
  match self.get_binding(x) {
    TmAbb(_, Some(ty)) => ty
    Var(ty) => ty
    _ => panic()
  }
}
