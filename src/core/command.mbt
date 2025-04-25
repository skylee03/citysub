///|
pub(all) enum Command {
  Eval(@info.Info, Term)
  Bind(@info.Info, String, Binding)
}

///|
pub fn Command::execute!(self : Command, ctx : Context) -> Context {
  match self {
    Eval(_, t) => {
      let ty = t.derive_type!(ctx)
      let t_prime = t.eval(ctx)
      println("\{t_prime.to_string(ctx)}\n  : \{ty.to_string(ctx)}")
      ctx
    }
    Bind(info, x, bind) => {
      let bind_prime = bind.derive_type!(ctx, info).eval(ctx)
      println("\{x} \{bind_prime.to_string(ctx)}")
      ctx.add_binding(x, bind_prime)
    }
  }
}
