use std::iter::Peekable;
use std::str::Chars;

fn main() {
    let tokens = &mut lex("program kissa; var i : integer; begin var j : integer; end.");
    println!("{:?}", tokens);
    println!(
        "{:?}",
        parse_program(tokens)
    );
}

//////////////////////////////////////////////////////////////////////////////
// LEXER /////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
#[derive(Clone)]
enum TokenValue {
    String(String),
    Integer(i32),
    Real(f32),
    Word(String),
    Whitespace(String),
}

#[derive(Debug)]
#[derive(Clone)]
struct Token {
    value: TokenValue,
    line: i32,
}

#[derive(Debug)]
struct TokenList {
    tokens: Vec<Token>,
    place: usize
}

impl TokenList {
    fn peek(&self) -> Option<Token> {
        let mut i = self.place;
        while i < self.tokens.len() {
            match self.tokens[i].value {
                TokenValue::Whitespace(_) => {i += 1; continue;},
                _ => return Some(self.tokens[i].clone())
            }
            i += 1;
        }
        None
    }

    fn next(&mut self) -> Option<Token> {
        let val = self.peek();
        self.place += 1; // TODO whitespacet
        val
    }

    fn eof(&self) -> bool {
        self.place >= self.tokens.len()
    }

    fn error_context(&self, place: usize) -> String {
        let token = &self.tokens[if place == 0 {place} else {place-1}];
        format!("[line {}, token {:?}]", token.line, token.value)
    }

    fn next_is(&self, kw: &str) -> bool {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.peek() {
            kw == word
        }
        else {
            false
        }
    }

    fn next_in(&self, kws: &[&str]) -> bool {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.peek() {
            kws.contains(&word.as_str())
        }
        else {
            false
        }
    }

    fn accept(&mut self, kw: &str) {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.next() {
            if word == kw {
                return;
            }
        }
        panic!("{} expected `{}'", self.error_context(self.place), kw);
    }

    fn try_accept(&mut self, kw: &str) -> bool {
        if self.next_is(kw) {
            self.next();
            true
        } else {
            false
        }
    }

    fn accept_identifier(&mut self) -> String {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.next() {
            return word;
        }
        panic!("{} expected identifier", self.error_context(self.place));
    }

    fn accept_integer(&mut self) -> i32 {
        if let Some(Token { value: TokenValue::Integer(i), line: _ }) = self.next() {
            return i;
        }
        panic!("{} expected integer", self.error_context(self.place));
    }

    fn unexpected(&self) {
        panic!("{} unexpected token", self.error_context(self.place));
    }
}

fn is_valid_identifier_char(chr: char) -> bool {
    return chr.is_alphanumeric() || chr == '_';
}

fn lex(code: &str) -> TokenList {
    let mut tokens = Vec::new();
    let mut chars = code.chars().peekable();
    let mut line = 1;
    while let Some(&chr) = chars.peek() {
        if chr.is_alphabetic() || chr == '_' {
            tokens.push(Token {
                value: TokenValue::Word(parse_token(&mut chars, is_valid_identifier_char)),
                line: line,
            })
        } else if chr.is_numeric() {
            tokens.push(Token {
                value: parse_number(&mut chars),
                line: line,
            });
        } else if chr.is_whitespace() {
            let whitespace = parse_token(&mut chars, char::is_whitespace);
            /*tokens.push(Token {
                value: TokenValue::Whitespace(whitespace.clone()),
                line: line,
            });*/
            line += whitespace.matches("\n").count() as i32;
        } else {
            tokens.push(Token {
                value: TokenValue::Word(parse_token(&mut chars, |c| {
                    !is_valid_identifier_char(c) && !c.is_whitespace()
                })),
                line: line,
            });
        }
    }
    return TokenList { tokens: tokens, place: 0 };
}

fn next_is<F>(chars: &mut Peekable<Chars>, f: F) -> bool
where
    F: FnOnce(char) -> bool,
{
    if let Some(&c) = chars.peek() {
        f(c)
    } else {
        false
    }
}

fn parse_number(chars: &mut Peekable<Chars>) -> TokenValue {
    let integer_part = parse_integer(chars);
    if let Some(&'.') = chars.peek() {
        chars.next();
        if !next_is(chars, char::is_numeric) {
            panic!("Lexical error: expected a real number literal");
        }
        let fractional_str = parse_token(chars, char::is_numeric);
        let fractional_part =
            fractional_str.parse::<i32>().unwrap() as f32 / 10f32.powi(fractional_str.len() as i32);
        let number = integer_part as f32 + fractional_part;
        if let Some(&'e') = chars.peek() {
            chars.next();
            TokenValue::Real(number * 10f32.powi(parse_integer(chars)))
        } else {
            TokenValue::Real(number)
        }
    } else {
        TokenValue::Integer(integer_part)
    }
}

fn parse_integer(chars: &mut Peekable<Chars>) -> i32 {
    parse_token(chars, char::is_numeric).parse::<i32>().unwrap()
}

fn parse_token<F>(chars: &mut Peekable<Chars>, f: F) -> String
where
    F: Fn(char) -> bool,
{
    let mut word = String::new();
    while let Some(&c) = chars.peek() {
        if f(c) {
            word.push(c);
            chars.next();
        } else {
            break;
        }
    }
    return word;
}

//////////////////////////////////////////////////////////////////////////////
// PARSER ////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

#[derive(Clone)]
#[derive(Debug)]
enum Type {
    Boolean(),
    Integer(),
    Real(),
    String(),
    Array(Box<Type>, i32),
    Void()
}

#[derive(Debug)]
enum Definition {
    Function(String, Vec<Parameter>, Type, Vec<Statement>),
    Variable(String, Type)
}

#[derive(Debug)]
struct Parameter {
    name: String,
    vtype: Type,
    is_ref: bool
}

#[derive(Debug)]
enum Statement {
    Definition(Definition),
    Assign(ExpressionBox, ExpressionBox),
    SimpleReturn(),
    Return(ExpressionBox),
    IfElse(ExpressionBox, Box<Statement>, Box<Statement>),
    While(ExpressionBox, Box<Statement>),
    Block(Vec<Statement>),
    Expression(ExpressionBox),
    Nop()
}

#[derive(Debug)]
struct ExpressionBox {
    expr: Box<Expression>
}

#[derive(Debug)]
enum Expression {
    Integer(i32),
    Real(f32),
    BiOperator(BinaryOperator, ExpressionBox, ExpressionBox),
    UnOperator(UnaryOperator, ExpressionBox),
    Call(String, Vec<ExpressionBox>),
    Index(ExpressionBox, ExpressionBox),
    Variable(String)
}

#[derive(Debug)]
enum BinaryOperator {
    Eq, Neq, Lt, Leq, Gt, Geq,
    Add, Sub, Mul, Div, Mod,
    And, Or
}

#[derive(Debug)]
enum UnaryOperator {
    Plus, Minus, Not, Size
}

fn parse_program(tokens: &mut TokenList) -> Vec<Statement> {
    tokens.accept("program");
    let id = tokens.accept_identifier();
    tokens.accept(";");
    let mut block = parse_block(tokens);
    tokens.accept(".");
    return block;
}

fn parse_block(tokens: &mut TokenList) -> Vec<Statement> {
    let mut stmts = Vec::new();
    stmts.extend(parse_statement(tokens));
    while tokens.try_accept(";") {
        if tokens.next_is("end") {
            break;
        }
        stmts.extend(parse_statement(tokens))
    }
    return stmts;
}

fn parse_type(tokens: &mut TokenList) -> Type {
    let typename = tokens.accept_identifier();
    match &typename[..] {
        "Boolean" => Type::Boolean(),
        "integer" => Type::Integer(),
        "real" => Type::Real(),
        "string" => Type::String(),
        "array" => {
            tokens.accept("[");
            let size = tokens.accept_integer();
            tokens.accept("]");
            tokens.accept("of");
            let subtype = parse_type(tokens);
            Type::Array(Box::new(subtype), size)
        }
        _ => panic!("syntax error")
    }
}

fn parse_statement(tokens: &mut TokenList) -> Vec<Statement> {
    if let Some(Token { value: val, line: line }) = tokens.peek() {
        match val {
            TokenValue::Word(kw) => match &kw[..] {
                "procedure" => vec![parse_function_def(tokens, true)],
                "function" => vec![parse_function_def(tokens, false)],
                "var" => parse_variable_def(tokens),
                "return" => vec![parse_return(tokens)],
                "if" => vec![parse_if(tokens)],
                "while" => vec![parse_while(tokens)],
                "begin" => {
                    tokens.accept("begin");
                    let m = vec![Statement::Block(parse_block(tokens))];
                    tokens.accept("end");
                    m
                },
                _ => vec![Statement::Expression(parse_expression(tokens))]
            },
            _ => panic!("")
        }
    }
    else {
        panic!("");
    }
}

fn parse_single_statement(tokens: &mut TokenList) -> Statement {
    let place = tokens.place;
    let mut statements = parse_statement(tokens);
    if statements.len() != 1 {
        panic!("{} invalid statement", tokens.error_context(place));
    }
    statements.pop().unwrap()
}

fn parse_function_def(tokens: &mut TokenList, is_proc: bool) -> Statement {
    tokens.accept(if is_proc {"procedure"} else {"function"});
    let name = tokens.accept_identifier();
    tokens.accept("(");
    let parameters = parse_parameters(tokens);
    let vtype = if is_proc {
        Type::Void()
    } else {
        tokens.accept(":");
        parse_type(tokens)
    };
    tokens.accept("begin");
    let body = parse_block(tokens);
    tokens.accept("end");
    Statement::Definition(Definition::Function(name, parameters, vtype, body))
}

fn parse_parameters(tokens: &mut TokenList) -> Vec<Parameter> {
    let mut params = Vec::new();
    if !tokens.next_is(")") {
        params.push(parse_parameter(tokens));
        while tokens.try_accept(",") {
            params.push(parse_parameter(tokens));
        }
    }
    params
}

fn parse_parameter(tokens: &mut TokenList) -> Parameter {
    let is_ref = tokens.try_accept("var");
    let name = tokens.accept_identifier();
    tokens.accept(":");
    let vtype = parse_type(tokens);
    Parameter { name: name, vtype: vtype, is_ref: is_ref }
}

fn parse_variable_def(tokens: &mut TokenList) -> Vec<Statement> {
    tokens.accept("var");
    let mut names = Vec::new();
    names.push(tokens.accept_identifier());
    while tokens.try_accept(",") {
        names.push(tokens.accept_identifier());
    }
    tokens.accept(":");
    let vtype = parse_type(tokens);
    names.into_iter().map(|n| Statement::Definition(Definition::Variable(n, vtype.clone()))).collect()
}

fn parse_return(tokens: &mut TokenList) -> Statement {
    tokens.accept("return");
    if tokens.next_is(";") || tokens.next_is("end") {
        Statement::SimpleReturn()
    } else {
        Statement::Return(parse_expression(tokens))
    }
}

fn parse_if(tokens: &mut TokenList) -> Statement {
    tokens.accept("if");
    let cond = parse_expression(tokens);
    tokens.accept("then");
    let then = parse_single_statement(tokens);
    let otherwise = if tokens.try_accept("else") {
        parse_single_statement(tokens)
    } else {
        Statement::Nop()
    };
    Statement::IfElse(cond, Box::new(then), Box::new(otherwise))
}

fn parse_while(tokens: &mut TokenList) -> Statement {
    tokens.accept("while");
    let cond = parse_expression(tokens);
    tokens.accept("do");
    let body = parse_single_statement(tokens); // TODO
    Statement::While(cond, Box::new(body))
}

fn parse_binary_operator(operator: String) -> BinaryOperator {
    match &operator[..] {
        "<" => BinaryOperator::Lt,
        ">" => BinaryOperator::Gt,
        "<=" => BinaryOperator::Leq,
        ">=" => BinaryOperator::Geq,
        "<>" => BinaryOperator::Neq,
        "=" => BinaryOperator::Eq,

        "+" => BinaryOperator::Add,
        "-" => BinaryOperator::Sub,
        "*" => BinaryOperator::Mul,
        "/" => BinaryOperator::Div,
        "%" => BinaryOperator::Mod,

        "and" => BinaryOperator::And,
        "or" => BinaryOperator::Or,
        _ => panic!()
    }
}

fn parse_unary_operator(operator: String) -> UnaryOperator {
    match &operator[..] {
        "+" => UnaryOperator::Plus,
        "-" => UnaryOperator::Minus,
        "not" => UnaryOperator::Not,
        _ => panic!()
    }
}

macro_rules! precedence_level {
    ($name:ident, $subexpr_parser:ident, $operator_list:expr) => {
        fn $name(tokens: &mut TokenList) -> ExpressionBox {
            let mut lhs = $subexpr_parser(tokens);
            while tokens.next_in($operator_list) {
                if let Some(Token { value: TokenValue::Word(kw), line: _ }) = tokens.next() {
                    let operator = parse_binary_operator(kw);
                    lhs = ExpressionBox { expr: Box::new(Expression::BiOperator(operator, lhs, $subexpr_parser(tokens))) };
                } else {
                    panic!();
                }
            }
            lhs
        }
    };
}

precedence_level!(parse_expression, parse_simple_expression, &["=", "<>", "<", ">", "<=", ">="]);
precedence_level!(parse_simple_expression, parse_term, &["+", "-", "or"]);
precedence_level!(parse_term, parse_size, &["*", "/", "%", "and"]);

fn parse_size(tokens: &mut TokenList) -> ExpressionBox {
    let mut lhs = parse_factor(tokens);
    while tokens.next_is(".") {
        tokens.accept(".");
        tokens.accept("size");
        lhs = ExpressionBox { expr: Box::new(Expression::UnOperator(UnaryOperator::Size, lhs)) };
    }
    lhs
}

fn parse_factor(tokens: &mut TokenList) -> ExpressionBox {
    match tokens.next() {
        Some(Token { value: TokenValue::Word(word), line: _ }) => {
            if word == "(" {
                let expr = parse_expression(tokens);
                tokens.accept(")");
                return expr;
            }
            if word == "not" {
                let expr = parse_factor(tokens);
                return expr;
            }
            if let Some(Token { value: TokenValue::Word(word2), line: _ }) = tokens.peek() {
                match &word2[..] {
                    "(" => {
                        // FUNCTION CALL
                        unimplemented!();
                    },
                    "[" => {
                        // INDEX
                        unimplemented!();
                    },
                    _ => {
                        return ExpressionBox { expr: Box::new(Expression::Variable(word)) };
                    }
                }
            }
            else {
                return ExpressionBox { expr: Box::new(Expression::Variable(word)) };
            }
        },
        Some(Token { value: TokenValue::Integer(x), line: _ }) => {
            return ExpressionBox { expr: Box::new(Expression::Integer(x)) };
        },
        Some(Token { value: TokenValue::Real(x), line: _ }) => {
            return ExpressionBox { expr: Box::new(Expression::Real(x)) };
        },
        _ => panic!("syntax error")
    }
}