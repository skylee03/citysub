///|
fn main {
  let argv = @sys.get_cli_args()
  let fname = @ref.new("")
  let mode = @ref.new("full")
  let usage = " usage: \{argv[0]} [options]"
  @ArgParser.parse(
    [
      ("--file", "-f", Set_string(fname), "source file name"),
      ("--mode", "-m", Set_string(mode), "subtyping mode"),
    ],
    ignore,
    usage,
    argv,
  )
  if fname.val == "" {
    println("Error: file name is not specified")
    return
  }
  try {
    @fs.read_file_to_string!(fname.val) |> @interpreter.interpret(mode.val)
  } catch {
    @fs.IOError(_) => println("Error: cannot read file \"\{fname.val}\"")
    _ => panic()
  }
}
