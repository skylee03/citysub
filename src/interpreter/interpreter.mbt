///|
pub fn interpret(code : String, mode : String) -> Unit {
  try {
    @core.set_mode!(mode)
    loop
      (@core.Context::empty(), @parser.parse!(code)!(@core.Context::empty()).0) {
      (_, Nil) => break ()
      (ctx, Cons(c, rest)) => continue (c.execute!(ctx), rest)
    }
  } catch {
    @info.ErrorWithInfo((msg, info)) => println("Error: \{info} \{msg}")
    _ => panic()
  }
}
