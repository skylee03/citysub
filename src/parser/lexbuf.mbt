///|
priv struct StringLexbuf {
  data : String
  end : Int
  mut position : Int
  mut line_number : Int
  mut line_position : Int
}

///|
fn StringLexbuf::get_position(self : StringLexbuf, position : Int) -> Position {
  { lnum: self.line_number, cnum: position - self.line_position + 1 }
}

///|
fn StringLexbuf::from_string(string : String) -> StringLexbuf {
  StringLexbuf::{
    data: string,
    end: string.length(),
    position: 0,
    line_number: 1,
    line_position: 0,
  }
}

///|
fn StringLexbuf::next_as_int(self : StringLexbuf) -> Int {
  if self.position >= self.end {
    return -1
  }
  let char = self.data.unsafe_char_at(self.position)
  self.position += 1
  if char == '\n' && self.position > self.line_position {
    self.line_number += 1
    self.line_position = self.position
  }
  return char.to_int()
}

///|
fn StringLexbuf::curr_pos(self : StringLexbuf) -> Int {
  self.position
}

///|
fn StringLexbuf::reset(self : StringLexbuf, pos~ : Int) -> Unit {
  self.position = pos
}

///|
fn StringLexbuf::get_char(self : StringLexbuf, start : Int, _end : Int) -> Char {
  self.data.unsafe_char_at(start)
}

///|
fn StringLexbuf::get_string(
  self : StringLexbuf,
  start : Int,
  end : Int
) -> String {
  self.data.substring(start~, end~)
}
