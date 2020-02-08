use std::str::Chars;

pub const EOF_CHAR: char = '\0';

pub struct Cursor<'a> {
    s: &'a str,
    chars: Chars<'a>,
    last_pos: usize,
    initial_len: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(input: &'a str) -> Cursor<'a> {
        Cursor {
            initial_len: input.len(),
            last_pos: 0,
            s: input,
            chars: input.chars(),
        }
    }

    fn rem(&self) -> &'a str {
        &self.s[self.last_pos..]
    }

    fn nth_char(&self, n: usize) -> char {
        self.chars().nth(n).unwrap_or(EOF_CHAR)
    }

    pub(crate) fn first(&self) -> char {
        self.nth_char(0)
    }

    pub(crate) fn second(&self) -> char {
        self.nth_char(1)
    }

    fn chars(&self) -> Chars<'a> {
        self.chars.clone()
    }

    /// Moves to the next character.
    pub(crate) fn bump(&mut self) -> Option<char> {
        self.chars.next()
    }

    pub fn is_eof(&self) -> bool {
        self.chars.as_str().is_empty()
    }

    pub fn len_consumed(&self) -> usize {
        self.initial_len - self.chars.as_str().len()
    }

    pub fn reset(&mut self) {
        self.last_pos = self.len_consumed();
    }

    pub fn take_collected(&mut self) -> String {
        let i = self.len_consumed();
        let s = self.s[self.last_pos..i].to_owned();
        self.last_pos = i;
        s
    }
}
