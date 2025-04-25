///|
pub(all) struct Position {
  lnum : Int
  cnum : Int
}

///|
pub impl Show for Position with output(self, logger) {
  logger.write_string("\{self.lnum}:\{self.cnum}")
}

///|
pub(all) enum Info {
  FI(Position, Position)
  UNKNOWN
}

///|
pub impl Show for Info with output(self, logger) {
  match self {
    FI(start, end) =>
      if start.lnum == end.lnum && start.cnum >= end.cnum - 1 {
        logger.write_string("[\{start}]")
      } else {
        logger.write_string("[\{start}-\{end.lnum}:\{end.cnum - 1}]")
      }
    UNKNOWN => ()
  }
}

///|
pub(all) type! ErrorWithInfo (String, Info)

///|
pub fn error_info![T](msg : String, info~ : Info = UNKNOWN) -> T {
  raise ErrorWithInfo((msg, info))
}
