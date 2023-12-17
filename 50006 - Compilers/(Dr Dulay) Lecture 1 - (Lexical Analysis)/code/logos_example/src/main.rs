use logos::Logos;
use std::{
    i32,
    io::{self, Write},
};

/// Simple program to take user input and deliver tokens.
fn main() {
    let mut user_input = String::new();
    println!(
        "Welcome to the expression tokenizer!\nType exit to exit, or an expression to tokenize"
    );

    loop {
        print!("Lex the expression: ");
        io::stdout().flush().unwrap();
        user_input.clear();
        io::stdin().read_line(&mut user_input).unwrap();
        if user_input.trim() == "exit" {
            break;
        }
        println!("The lexer returned: {:?}", tokenize(&user_input))
    }
}

/// Tokenizing the input using the Logos library.
#[derive(Logos, Debug, PartialEq)]
enum Token {
    #[token("*")]
    Mul,

    #[token("/")]
    Div,

    #[token("+")]
    Plus,

    #[token("-")]
    Minus,

    // Allows for denary, binary and hex numbers.
    #[regex("0b-?[0|1]+", |lex| i32::from_str_radix(&lex.slice()[2..], 2))]
    #[regex("0x-?[a-f|0-9]+", |lex| i32::from_str_radix(&lex.slice()[2..], 16))]
    #[regex("-?[0-9]+", |lex| lex.slice()[0..].parse())]
    Num(i32),

    #[regex("[a-z|A-Z]+", |lex| lex.slice()[0..].parse())]
    Ident(String),

    #[error]
    #[regex(r"[ \r\t\n\f]", logos::skip)] // ignoring/skipping whitespace.
    Error,
}

/// Tokenize a string into symbols for Plus, Minus, Divide and Multiply,
/// Numbers and Identifiers.
fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut lex = Token::lexer(input);
    let mut tokens = Vec::new();

    while let Some(tok) = lex.next() {
        match tok {
            Token::Error => return Err(String::from("Could not tokenize")),
            other => tokens.push(other),
        }
    }

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenizer_general() {
        assert_eq!(
            tokenize("a+a+b+0b11").unwrap(),
            vec![
                Token::Ident(String::from("a")),
                Token::Plus,
                Token::Ident(String::from("a")),
                Token::Plus,
                Token::Ident(String::from("b")),
                Token::Plus,
                Token::Num(3)
            ]
        )
    }

    #[test]
    #[should_panic]
    fn test_tokenizer_unexpected() {
        tokenize("a+?").unwrap();
    }

    #[test]
    fn test_tokenizer_hex_nums() {
        assert_eq!(tokenize("0x10").unwrap(), vec![Token::Num(16)]);
        assert_eq!(tokenize("0x-10").unwrap(), vec![Token::Num(-16)]);
        assert_eq!(tokenize("0x1a").unwrap(), vec![Token::Num(26)]);
        assert_eq!(tokenize("0x-1a").unwrap(), vec![Token::Num(-26)]);
        assert_eq!(tokenize("0x00a").unwrap(), vec![Token::Num(10)]);
        assert_eq!(tokenize("0x-00a").unwrap(), vec![Token::Num(-10)]);

        // Should not parse as a hexadecimal (gh are not valid), but instead as a
        // 0 followed by "xgh" identifier.
        assert_eq!(
            tokenize("0xgh").unwrap(),
            vec![Token::Num(0), Token::Ident(String::from("xgh"))]
        );
    }

    #[test]
    fn test_tokenizer_binary_nums() {
        assert_eq!(tokenize("0b10").unwrap(), vec![Token::Num(2)]);
        assert_eq!(tokenize("0b-10").unwrap(), vec![Token::Num(-2)]);
        assert_eq!(tokenize("0b0000").unwrap(), vec![Token::Num(0)]);
        assert_eq!(tokenize("0b-0000").unwrap(), vec![Token::Num(0)]);
        assert_eq!(tokenize("0b1010").unwrap(), vec![Token::Num(10)]);
        assert_eq!(tokenize("0b-1010").unwrap(), vec![Token::Num(-10)]);

        // Should split string into identifier sandwiched by numbers
        assert_eq!(
            tokenize("0b3").unwrap(),
            vec![
                Token::Num(0),
                Token::Ident(String::from("b")),
                Token::Num(3)
            ]
        );
    }

    #[test]
    fn test_tokenizer_nums() {
        assert_eq!(tokenize("73").unwrap(), vec![Token::Num(73)]);
        assert_eq!(tokenize("-73").unwrap(), vec![Token::Num(-73)]);
        assert_eq!(tokenize("0").unwrap(), vec![Token::Num(0)]);
        assert_eq!(tokenize("-0").unwrap(), vec![Token::Num(0)]);
        assert_eq!(tokenize("10").unwrap(), vec![Token::Num(10)]);
        assert_eq!(tokenize("-10").unwrap(), vec![Token::Num(-10)]);

        // Should split string into identifier sandwiched by numbers
        assert_eq!(
            tokenize("0abc3").unwrap(),
            vec![
                Token::Num(0),
                Token::Ident(String::from("abc")),
                Token::Num(3)
            ]
        );
    }

    #[test]
    fn test_tokenizer_idents() {
        assert_eq!(
            tokenize("abcde+abc").unwrap(),
            vec![
                Token::Ident(String::from("abcde")),
                Token::Plus,
                Token::Ident(String::from("abc"))
            ]
        );
        assert_eq!(
            tokenize("abcde0abc").unwrap(),
            vec![
                Token::Ident(String::from("abcde")),
                Token::Num(0),
                Token::Ident(String::from("abc"))
            ]
        );
    }
}
