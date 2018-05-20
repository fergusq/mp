use std::io::Read;
use std::fs::File;
use std::env;
use std::fmt::Write;
use std::iter::Peekable;
use std::str::Chars;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: mp <file>");
        return;
    }

    let filename = &args[1];
    
    // luetaan koodi tiedostosta
    let mut file = File::open(filename).unwrap();
    let mut code = String::new();
    file.read_to_string(&mut code).unwrap();
    
    // lisätään builtinit nimitauluun
    let mut nt = Nametable::new(Type::Void);
    let mut builtins = String::new();
    nt.push();
    add_builtins(&mut nt, &mut builtins);
    
    // jäsennetään ohjelma
    let tokens = &mut lex(&code);
    let mut tree = parse_program(tokens);
    
    // semanttinen analyysi
    analyse_stmt(&mut tree, &mut nt, true);
    
    // koodigeneraatio
    // ylätason koodi laitetaan uuden main-funktion sisään
    let mut cg = CodeGenerator::new();
    cg.queue.push(Definition::Function(String::from("main"), Vec::new(), Type::Void, Rc::new(RefCell::new(tree))));
    while !cg.queue.is_empty() {
        let queue = cg.queue.clone();
        cg.queue.clear();
        for def in queue {
            cg.generate_def(def);
        }
    }
    
    // tulostetaan ulostulo
    println!("#include <stdlib.h>");
    println!("#include <stdio.h>");
    println!("#include <assert.h>");
    println!("void *tmp_array;");
    println!("#define make_array(size, type) (tmp_array = malloc(size*sizeof(type)+sizeof(int)), tmp_array = (int*) tmp_array + 1, array_len(tmp_array) = size, tmp_array)");
    println!("#define array_len(a) ((int*)(a))[-1]");
    println!("{}", builtins);
    println!("{}", cg.header);
    println!("{}", cg.output);
}

// BUILTINS

fn add_builtins(nt: &mut Nametable, output: &mut String) {
    // lisätään arraynluontifunktiot
    add_make_array_builtin(nt, output, Type::Integer);
    add_make_array_builtin(nt, output, Type::Real);
    add_make_array_builtin(nt, output, Type::String);
    add_make_array_builtin(nt, output, Type::Boolean);
    // lisätään tyyppimuunnosfunktiot
    add_cast_builtin(nt, output, Type::Integer, Type::Real);
    add_cast_builtin(nt, output, Type::Real, Type::Integer);
    
    // lisätään assert-funktio
    nt.peek().insert(String::from("assert"), Definition::Function(
        String::from("assert"),
        vec![Parameter::new(String::from("condition"), Type::Boolean, false)],
        Type::Void,
        Rc::new(RefCell::new(Statement::Nop))
    ));
}

fn add_make_array_builtin(nt: &mut Nametable, output: &mut String, vtype: Type) {
    let name = format!("make_{}_array", vtype);
    nt.peek().insert(name.clone(), Definition::Function(
        name.clone(),
        vec![Parameter::new(String::from("size"), Type::Integer, false)],
        Type::Array(Box::new(vtype.clone()), -1),
        Rc::new(RefCell::new(Statement::Nop))
    ));
    write!(output, "#define {}(size) make_array(size, {})\n", name, vtype.to_c(&String::new())).unwrap();
}

fn add_cast_builtin(nt: &mut Nametable, output: &mut String, a: Type, b: Type) {
    let name = format!("{}_to_{}", a, b);
    nt.peek().insert(name.clone(), Definition::Function(
        name.clone(),
        vec![Parameter::new(String::from("val"), a, false)],
        b.clone(),
        Rc::new(RefCell::new(Statement::Nop))
    ));
    write!(output, "#define {}(val) (({})(val))\n", name, b.to_c(&String::new())).unwrap();
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
    // peek palauttaa seuraavan tokenin, mutta ei poista sitä jonosta
    fn peek(&self) -> Option<Token> {
        let mut i = self.place;
        while i < self.tokens.len() {
            match self.tokens[i].value {
                TokenValue::Whitespace(_) => {i += 1; continue;},
                _ => return Some(self.tokens[i].clone())
            }
        }
        None
    }

    // next palauttaa seuraavan tokenin ja poistaa sen jonosta
    fn next(&mut self) -> Option<Token> {
        let val = self.peek();
        self.place += 1; // TODO whitespacet
        val
    }

    // kertoo, onko tokeneita jäljellä
    fn eof(&self) -> bool {
        self.place >= self.tokens.len()
    }

    // palauttaa merkkijonon, jossa on rivinumero ja nykyinen token virheviestejä varten
    fn error_context(&self, place: usize) -> String {
        let token = &self.tokens[if place == 0 {place} else {place-1}];
        format!("[line {}, token {:?}]", token.line, token.value)
    }

    // palauttaa truen tai falsen, jos seuraava token on sama kuin annettu merkkijono
    fn next_is(&self, kw: &str) -> bool {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.peek() {
            kw == word
        }
        else {
            false
        }
    }

    // kertoo, onko seuraava token jokin annetuista merkkijonoista
    fn next_in(&self, kws: &[&str]) -> bool {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.peek() {
            kws.contains(&word.as_str())
        }
        else {
            false
        }
    }

    // panikoi, jos seuraava token ei ole annettu merkkijono
    fn accept(&mut self, kw: &str) {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.next() {
            if word == kw {
                return;
            }
        }
        panic!("{} expected `{}'", self.error_context(self.place), kw);
    }

    // sama kuin next_is, mutta poistaa tokenin jonosta jos se on sama kuin annettu merkkijono
    fn try_accept(&mut self, kw: &str) -> bool {
        if self.next_is(kw) {
            self.next();
            true
        } else {
            false
        }
    }

    // palauttaa seuraavan identifierin (TODO: validoi, että identifier koostuu sallituista merkeistä) tai panikoi
    fn accept_identifier(&mut self) -> String {
        if let Some(Token { value: TokenValue::Word(word), line: _ }) = self.next() {
            return word;
        }
        panic!("{} expected identifier", self.error_context(self.place));
    }

    // palauttaa seuraavan kokonaisluvun tai panikoi
    fn accept_integer(&mut self) -> i32 {
        if let Some(Token { value: TokenValue::Integer(i), line: _ }) = self.next() {
            return i;
        }
        panic!("{} expected integer", self.error_context(self.place));
    }

    // tulostaa virheviestin
    fn unexpected(&self) -> ! {
        panic!("{} unexpected token", self.error_context(self.place))
    }
}

// funktio, joka kertoo onko annettu merkki validi osa identifieriä (alfanumeerinen tai _)
fn is_valid_identifier_char(chr: char) -> bool {
    return chr.is_alphanumeric() || chr == '_';
}

// funktio, joka kertoo onko annettu merkki validi osa pitkää operaattoria (=, >=, <>, :=)
fn is_valid_operator_char(chr: char) -> bool {
    return ['<', '>', '=', ':'].contains(&chr);
}

// skannaa koodin ja palauttaa TokenList-olion
fn lex(code: &str) -> TokenList {
    let mut tokens = Vec::new();
    let mut chars = code.chars().peekable();
    let mut line = 1;
    while let Some(&chr) = chars.peek() {
        // identifier
        if chr.is_alphabetic() || chr == '_' {
            tokens.push(Token {
                value: TokenValue::Word(parse_token(&mut chars, is_valid_identifier_char).to_lowercase()),
                line: line,
            })
        // pitkä operaattori
        } else if is_valid_operator_char(chr) {
            tokens.push(Token {
                value: TokenValue::Word(parse_token(&mut chars, is_valid_operator_char)),
                line: line,
            })
        // kokonaisluku tai liukuluku
        } else if chr.is_numeric() {
            tokens.push(Token {
                value: parse_number(&mut chars),
                line: line,
            });
        // merkkijono
        } else if chr == '"' {
            tokens.push(Token {
                value: TokenValue::String(parse_string(&mut chars)),
                line: line,
            });
        // kommentti (TODO)
        } else if chr == '{' {
            let comment = parse_comment(&mut chars);
            line += comment.matches("\n").count() as i32;
        // whitespace-token (TODO)
        } else if chr.is_whitespace() {
            let whitespace = parse_token(&mut chars, char::is_whitespace);
            /*tokens.push(Token {
                value: TokenValue::Whitespace(whitespace.clone()),
                line: line,
            });*/
            line += whitespace.matches("\n").count() as i32;
        // lyhyt operaattori
        } else {
            chars.next();
            tokens.push(Token {
                value: TokenValue::Word(chr.to_string()),
                line: line,
            });
        }
    }
    return TokenList { tokens: tokens, place: 0 };
}

// funktio, joka täyttääkö seuraava merkki annetun ehdon
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

// skannaa kokonaisluvun tai liukuluvun
fn parse_number(chars: &mut Peekable<Chars>) -> TokenValue {
    // luetaan ensin kokonaislukuosa
    let integer_part = parse_integer(chars);
    // jos seuraava merkki on desimaalipiste, luetaan desimaaliosa
    if let Some(&'.') = chars.peek() {
        chars.next();
        
        // luetaan desimaaliosa
        if !next_is(chars, char::is_numeric) {
            panic!("Lexical error: Expected a real number literal");
        }
        let fractional_str = parse_token(chars, char::is_numeric);
        
        // lasketaan lukuarvo
        let fractional_part =
            fractional_str.parse::<i32>().unwrap() as f32 / 10f32.powi(fractional_str.len() as i32);
        let number = integer_part as f32 + fractional_part;
        
        // jos seuraava merkki on e, korotetaan merkki annettuun kymmenpotenssiin
        if let Some(&'e') = chars.peek() {
            chars.next();
            if !next_is(chars, |c| char::is_numeric(c) || c == '+' || c == '-') {
                panic!("Lexical error: Expected an exponet literal");
            }
            let sign = match chars.peek() {
                Some(&'+') => {
                    chars.next();
                    1
                }
                Some(&'-') => {
                    chars.next();
                    -1
                }
                _ => 1
            };
            TokenValue::Real(number * 10f32.powi(sign*parse_integer(chars)))
        } else {
            TokenValue::Real(number)
        }
    // muulloin palautetaan kokonaisluku-token
    } else {
        TokenValue::Integer(integer_part)
    }
}

// lukee merkkejä niin kauan kun ne ovat numeerisia
fn parse_integer(chars: &mut Peekable<Chars>) -> i32 {
    if !next_is(chars, char::is_numeric) {
        panic!("Lexical error: Expected an integer number literal");
    }
    parse_token(chars, char::is_numeric).parse::<i32>().unwrap()
}

// lukee merkkejä niin kauan kun ne täyttävät annetun ehdon
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

// jäsentää merkkijonon
fn parse_string(chars: &mut Peekable<Chars>) -> String {
    let mut string = String::new();
    chars.next(); // avaava lainausmerkki
    while let Some(c) = chars.next() {
        if c == '"' {
            return string;
        } else if c == '\\' {
            let c = chars.next().unwrap();
            match c {
                'n' => string.push('\n'),
                '\\' => string.push('\\'),
                '"' => string.push('"'),
                x => string.push(x)
            }
        } else {
            string.push(c);
        }
    }
    panic!("Lexical error: Unclosed string");
}

// jäsentää kommentin
fn parse_comment(chars: &mut Peekable<Chars>) -> String {
    chars.next(); // avaava sulku
    if !next_is(chars, |c| c=='*') { panic!("Lexical error: Ungrammatical comment") }
    
    let mut comment = String::new();
    while let Some(c) = chars.next() {
        if c == '*' {
            if let Some(&'}') = chars.peek() {
                chars.next();
                return comment;
            }
        }
        comment.push(c);
    }
    panic!("Lexical error: Unclosed comment");
}

//////////////////////////////////////////////////////////////////////////////
// PARSER ////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
enum Type {
    Boolean,
    Integer,
    Real,
    String,
    Array(Box<Type>, i32),
    Void,
    Error
}

// toteutetaan Display, jotta Typen voi muuttaa merkkijonoksi
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Boolean => write!(f, "boolean"),
            Type::Integer => write!(f, "integer"),
            Type::Real => write!(f, "real"),
            Type::String => write!(f, "string"),
            Type::Array(ref t, -1) => write!(f, "array of {}", t),
            Type::Array(ref t, i) => write!(f, "array [{}] of {}", i, t),
            Type::Void => write!(f, "void"),
            Type::Error => write!(f, "(unknown)")
        }
    }
}

#[derive(Clone)]
#[derive(Debug)]
enum Definition {
    Function(String, Vec<Parameter>, Type, Rc<RefCell<Statement>>),
    Variable(Parameter)
}

#[derive(Clone)]
#[derive(Debug)]
struct Parameter {
    name: String,
    vtype: Type,
    is_ref: bool
}

impl Parameter {
    fn new(name: String, vtype: Type, is_ref: bool) -> Parameter {
        Parameter { name: name, vtype: vtype, is_ref: is_ref }
    }
}

#[derive(Debug)]
enum Statement {
    Definition(Definition),
    SimpleReturn,
    Return(ExpressionBox),
    IfElse(ExpressionBox, Box<Statement>, Box<Statement>),
    While(ExpressionBox, Box<Statement>),
    Block(Vec<Statement>),
    Expression(ExpressionBox),
    Nop
}

#[derive(Debug)]
struct ExpressionBox {
    expr: Box<Expression>,
    etype: Type,
    make_ref: bool
}

impl ExpressionBox {
    fn new(expr: Expression) -> ExpressionBox {
        ExpressionBox { expr: Box::new(expr), etype: Type::Error, make_ref: false } 
    }
}

#[derive(Debug)]
enum Expression {
    Integer(i32),
    Real(f32),
    String(String),
    Assign(ExpressionBox, ExpressionBox),
    BiOperator(BinaryOperator, ExpressionBox, ExpressionBox),
    UnOperator(UnaryOperator, ExpressionBox),
    Call(String, String, Vec<ExpressionBox>),
    Index(String, ExpressionBox),
    Variable(String, Box<bool>)
}

#[derive(Debug)]
enum BinaryOperator {
    Eq, Neq, Lt, Leq, Gt, Geq,
    Add, Sub, Mul, Div, Mod,
    And, Or
}

// palauttaa tyypit, jotka voivat olla operaattorin operandin tyyppejä (analyysiä varten)
impl BinaryOperator {
    fn allowed_types(&self) -> Vec<Type> {
        let num_types = vec![Type::Integer, Type::Real];
        let bool_types = vec![Type::Boolean];
        match *self {
            BinaryOperator::Eq => num_types,
            BinaryOperator::Neq => num_types,
            BinaryOperator::Lt => num_types,
            BinaryOperator::Leq => num_types,
            BinaryOperator::Gt => num_types,
            BinaryOperator::Geq => num_types,
            BinaryOperator::Add => num_types,
            BinaryOperator::Sub => num_types,
            BinaryOperator::Mul => num_types,
            BinaryOperator::Div => num_types,
            BinaryOperator::Mod => num_types,
            BinaryOperator::And => bool_types,
            BinaryOperator::Or => bool_types
        }
    }
}

#[derive(Debug)]
enum UnaryOperator {
    Plus, Minus, Not, Size
}

impl UnaryOperator {
    fn allowed_types(&self) -> Vec<Type> {
        let num_types = vec![Type::Integer, Type::Real];
        match *self {
            UnaryOperator::Plus => num_types,
            UnaryOperator::Minus => num_types,
            UnaryOperator::Not => vec![Type::Boolean],
            UnaryOperator::Size => panic!("not implemented")
        }
    }
}

// parsii koko ohjelman
fn parse_program(tokens: &mut TokenList) -> Statement {
    tokens.accept("program");
    let _id = tokens.accept_identifier();
    tokens.accept(";");
    let block = parse_block(tokens);
    tokens.accept(".");
    return Statement::Block(block);
}

// parsii listan lauseita (ei begin- ja end-avainsanoja)
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

// parsii tyypin
fn parse_type(tokens: &mut TokenList) -> Type {
    let typename = tokens.accept_identifier();
    match &typename[..] {
        "boolean" => Type::Boolean,
        "integer" => Type::Integer,
        "real" => Type::Real,
        "string" => Type::String,
        "array" => {
            let size = if tokens.try_accept("[") {
                let size = tokens.accept_integer();
                tokens.accept("]");
                size
            } else {
                -1
            };
            tokens.accept("of");
            let subtype = parse_type(tokens);
            Type::Array(Box::new(subtype), size)
        }
        _ => tokens.unexpected()
    }
}

// parsii lauseen (ulostulona voi olla useita lauseita, sillä var-lauseet joissa on monta muuttujaa laajennetaan useiksi lauseksi)
fn parse_statement(tokens: &mut TokenList) -> Vec<Statement> {
    if let Some(Token { value: val, line: _ }) = tokens.peek() {
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
            _ => vec![Statement::Expression(parse_expression(tokens))]
        }
    }
    else {
        tokens.unexpected()
    }
}

// parsii lauseen ja varmistaa, että ulostulona on vain yksi lause
fn parse_single_statement(tokens: &mut TokenList) -> Statement {
    let place = tokens.place;
    let mut statements = parse_statement(tokens);
    if statements.len() != 1 {
        panic!("{} invalid statement", tokens.error_context(place));
    }
    statements.pop().unwrap()
}

// parsii funktion tai proseduurin
fn parse_function_def(tokens: &mut TokenList, is_proc: bool) -> Statement {
    tokens.accept(if is_proc {"procedure"} else {"function"});
    let name = tokens.accept_identifier();
    tokens.accept("(");
    let parameters = parse_parameters(tokens);
    tokens.accept(")");
    let vtype = if is_proc {
        Type::Void
    } else {
        tokens.accept(":");
        parse_type(tokens)
    };
    tokens.accept(";");
    let body = parse_single_statement(tokens);
    Statement::Definition(Definition::Function(name, parameters, vtype, Rc::new(RefCell::new(body))))
}

// parsii parametrilistan
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

// parsii yhden parametrin
fn parse_parameter(tokens: &mut TokenList) -> Parameter {
    let is_ref = tokens.try_accept("var");
    let name = tokens.accept_identifier();
    tokens.accept(":");
    let vtype = parse_type(tokens);
    Parameter::new(name, vtype, is_ref)
}

// parsii muuttujamäärityksen
fn parse_variable_def(tokens: &mut TokenList) -> Vec<Statement> {
    tokens.accept("var");
    let mut names = Vec::new();
    names.push(tokens.accept_identifier());
    while tokens.try_accept(",") {
        names.push(tokens.accept_identifier());
    }
    tokens.accept(":");
    let vtype = parse_type(tokens);
    names.into_iter().map(|n| Statement::Definition(Definition::Variable(Parameter::new(n, vtype.clone(), false)))).collect()
}

// parsii return-lauseen
fn parse_return(tokens: &mut TokenList) -> Statement {
    tokens.accept("return");
    if tokens.next_is(";") || tokens.next_is("end") {
        Statement::SimpleReturn
    } else {
        Statement::Return(parse_expression(tokens))
    }
}

// parsii if-lauseen
fn parse_if(tokens: &mut TokenList) -> Statement {
    tokens.accept("if");
    let cond = parse_expression(tokens);
    tokens.accept("then");
    let then = parse_single_statement(tokens);
    let otherwise = if tokens.try_accept("else") {
        parse_single_statement(tokens)
    } else {
        Statement::Nop
    };
    Statement::IfElse(cond, Box::new(then), Box::new(otherwise))
}

// parsii while-lauseen
fn parse_while(tokens: &mut TokenList) -> Statement {
    tokens.accept("while");
    let cond = parse_expression(tokens);
    tokens.accept("do");
    let body = parse_single_statement(tokens); // TODO
    Statement::While(cond, Box::new(body))
}

// palauttaa merkkijonoa vastaavan operaattoriolion
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

// palauttaa merkkijonoa vastaavan operaattoriolion
fn parse_unary_operator(operator: String) -> UnaryOperator {
    match &operator[..] {
        "+" => UnaryOperator::Plus,
        "-" => UnaryOperator::Minus,
        "not" => UnaryOperator::Not,
        _ => panic!()
    }
}

// makro, jonka pohjalta luodaan jokaista laskujärjestystasoa vastaava jäsennysfunktio
macro_rules! precedence_level {
//  funktion nimi, seuraavan tason jäsennin, operaattorit
    ($name:ident, $subexpr_parser:ident, $operator_list:expr) => {
        fn $name(tokens: &mut TokenList) -> ExpressionBox {
            // parsitaan seuraavan tason lauseke
            let mut lhs = $subexpr_parser(tokens);
            // niin kauan kun seuraavaksi tulee operaattori, parsitaan se ja seuraavan tason lauseke
            while tokens.next_in($operator_list) {
                if let Some(Token { value: TokenValue::Word(kw), line: _ }) = tokens.next() {
                    let operator = parse_binary_operator(kw);
                    lhs = ExpressionBox::new(Expression::BiOperator(operator, lhs, $subexpr_parser(tokens)));
                } else {
                    tokens.unexpected();
                }
            }
            // palautetaan lhs
            lhs
        }
    };
}

precedence_level!(parse_expression, parse_simple_expression, &["=", "<>", "<", ">", "<=", ">="]);
precedence_level!(parse_simple_expression, parse_term, &["+", "-", "or"]);
precedence_level!(parse_term, parse_size, &["*", "/", "%", "and"]);

// parsitaan .size-operaattori
fn parse_size(tokens: &mut TokenList) -> ExpressionBox {
    let mut lhs = parse_factor(tokens);
    while tokens.next_is(".") {
        tokens.accept(".");
        tokens.accept("size");
        lhs = ExpressionBox::new(Expression::UnOperator(UnaryOperator::Size, lhs));
    }
    lhs
}

// parsii tekijän
fn parse_factor(tokens: &mut TokenList) -> ExpressionBox {
    // luetaan token ja päätellään sen perusteella lausekkeen tyyppi
    match tokens.next() {
        Some(Token { value: TokenValue::Word(word), line: _ }) => {
            // sulkulauseke
            if word == "(" {
                let expr = parse_expression(tokens);
                tokens.accept(")");
                return expr;
            }
            // unaarioperaattori
            if word == "not" || word == "+" || word == "-" {
                let expr = parse_factor(tokens);
                return ExpressionBox::new(Expression::UnOperator(parse_unary_operator(word), expr));
            }
            // tutkitaan seuraavaa tokenia
            if let Some(Token { value: TokenValue::Word(word2), line: _ }) = tokens.peek() {
                let expr = match &word2[..] {
                    // funktiokutsu
                    "(" => {
                        tokens.accept("(");
                        let mut args = Vec::new();
                        if !tokens.next_is(")") {
                            args.push(parse_expression(tokens));
                            while tokens.try_accept(",") {
                                args.push(parse_expression(tokens));
                            }
                        }
                        tokens.accept(")");
                        ExpressionBox::new(Expression::Call(word, String::new(), args))
                    },
                    // arrayindeksointi
                    "[" => {
                        tokens.accept("[");
                        let index = parse_expression(tokens);
                        tokens.accept("]");
                        ExpressionBox::new(Expression::Index(word, index))
                    },
                    // jos seuraava token ei ole ( tai [, kyseessä on tavallinen muuttuja
                    _ => {
                        ExpressionBox::new(Expression::Variable(word, Box::new(false)))
                    }
                };
                // jos seuraava token on :=, parsitaan muuttuja-asetus
                return if tokens.try_accept(":=") {
                    let rexpr = parse_expression(tokens);
                    ExpressionBox::new(Expression::Assign(expr, rexpr))
                } else {
                    expr // palautetaan expr
                };
            }
            // jos seuraava token ei ollut identifier tai operaattori
            else {
                return ExpressionBox::new(Expression::Variable(word, Box::new(false)));
            }
        },
        // kokonaisluku
        Some(Token { value: TokenValue::Integer(x), line: _ }) => {
            return ExpressionBox::new(Expression::Integer(x));
        },
        // liukuluku
        Some(Token { value: TokenValue::Real(x), line: _ }) => {
            return ExpressionBox::new(Expression::Real(x));
        },
        // merkkijono
        Some(Token { value: TokenValue::String(x), line: _ }) => {
            return ExpressionBox::new(Expression::String(x));
        },
        // muulloin:
        _ => tokens.unexpected()
    }
}

//////////////////////////////////////////////////////////////////////////////
// SEMANTIC ANALYSIS /////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// symbolitaulutyyppi
struct Nametable {
    stack: Vec<HashMap<String, Definition>>,
    name_stack: Vec<i32>,
    counter_stack: Vec<i32>,
    return_type: Type
}

impl Nametable {
    fn new(return_type: Type) -> Nametable {
        Nametable { stack: Vec::new(), name_stack: Vec::new(), counter_stack: vec![0], return_type: return_type }
    }
    // lisää uuden "scopen"
    fn push(&mut self) {
        self.stack.push(HashMap::new());
        let last_index = self.counter_stack.len()-1;
        self.counter_stack[last_index] += 1;
        self.name_stack.push(*self.counter_stack.last().unwrap());
        self.counter_stack.push(0);
    }
    // poistaa ylimmän "scopen"
    fn pop(&mut self) {
        self.stack.pop();
        self.name_stack.pop();
        self.counter_stack.pop();
    }
    // palauttaa ylimmän "scopen"
    fn peek(&mut self) -> &mut HashMap<String, Definition> {
        self.stack.last_mut().unwrap()
    }
    // palauttaa nykyisen scopen nimen
    fn current_path(&self) -> String {
        let mut ans = String::new();
        for n in &*self.name_stack {
            write!(ans, "_{}", n).unwrap();
        }
        ans
    }
    // palauttaa symbolia vastaavan määritelmän
    fn find_definition(&self, name: &String) -> Option<&Definition> {
        // iteroidaan scopet
        let mut i = self.stack.len();
        while i > 0 {
            if let Some(def) = self.stack[i-1].get(name) {
                return Some(def);
            }
            i -= 1;
        }
        eprintln!("Semantic error: Symbol not found: {}", name);
        None
    }
}

// tarkistaa, ovatko tyypit yhteensopivia
fn check_types(a: &Type, b: &Type) -> bool {
    if *a == Type::Error || *b == Type::Error { // Error-tyyppi on yhteensopiva kaikkien kanssa
        true
    } else if let &Type::Array(ref t1, ref size1) = a { // arrayt ovat yhteensopivat, jos elementtien tyypit ovat yhteensopivat JA niillä on sama koko tai b:llä ei ole kokoa
        if let &Type::Array(ref t2, -1) = b {
            check_types(t1, t2)
        } else if let &Type::Array(ref t2, ref size2) = b {
            size1 == size2 && check_types(t1, t2)
        } else {
            false
        }
    } else {
        *a == *b
    }
}

// palauttaa truen tai falsen riippuen siitä, onko symboli varattu sana vai ei
fn check_identifier(ident: &String) {
    let is_keyword = match &ident[..] {
        "or" => true,
        "and" => true,
        "not" => true,
        "if" => true,
        "then" => true,
        "else" => true,
        "of" => true,
        "while" => true,
        "do" => true,
        "begin" => true,
        "end" => true,
        "var" => true,
        "array" => true,
        "procedure" => true,
        "function" => true,
        "program" => true,
        "assert" => true,
        "return" => true,
        _ => false
    };
    if is_keyword {
        eprintln!("Warning: Program is not Mini-Pascal 2018 compliant: use of keyword as identifier");
    }
}

// analysoi lohkon
fn analyse_block(block: &mut Vec<Statement>, nt: &mut Nametable, is_top: bool) {
    nt.push(); // uusi scope
    let mut block_count = 0;
    for stmt in &mut *block { // käydään läpi lauseet ja etsitään määritykset (definition) (pass 1)
        if let &mut Statement::Definition(ref mut def) = stmt {
            let name = match def {
                &mut Definition::Function(ref mut name, ref mut params, _, _) => {
                    if !is_top {
                        eprintln!("Warning: Program is not Mini-Pascal 2018 compliant: functions and procedures should be declared at the top level only");
                    }
                    
                    // etsitään nonlokaalit
                    let mut nonlocals = Vec::new();
                    for map in &nt.stack {
                        for (_name, def) in map {
                            match def {
                                &Definition::Variable(ref par) => {
                                    let new_par = Parameter::new(par.name.clone(), par.vtype.clone(), true);
                                    if !params.iter().any(|ref p| p.name == par.name) { /* lisätään muuttuja vain jos parametri ei varjosta sitä */
                                        nonlocals.push(new_par.clone());
                                    }
                                }
                                _ => {}
                            };
                        }
                    }
                    
                    // lisätään nonlokaalit parametreihin
                    params.extend(nonlocals);
                    
                    let old_name = name.clone();
                    
                    // lisätään nimen perään nykyisen scopen nimi
                    write!(name, "{}", nt.current_path()).unwrap();
                    
                    old_name
                },
                &mut Definition::Variable(Parameter { ref name, .. }) => name.clone()
            };
            nt.peek().insert(name, def.clone()); // lisätään määritelmä symbolitauluun
        }
        match stmt {
            &mut Statement::Block(_) => block_count += 1, // pidetään kirjaa lohkojen määrästä
            &mut Statement::Definition(_) => {}
            _ => {
                if is_top {
                    eprintln!("Warning: Program is not Mini-Pascal 2018 compliant: there should be only definitions and a block at the top level");
                }
            }
        }
        if !is_top {
            if let &mut Statement::Expression(ref expr) = stmt {
                match *expr.expr {
                    Expression::Call(_, _, _) => {}
                    Expression::Assign(_, _) => {}
                    _ => {
                        eprintln!("Warning: Program is not Mini-Pascal 2018 compliant: expression statements should be either calls or assignments");
                    }
                }
            }
        }
    }
    
    if is_top {
        if block_count != 1 {
            eprintln!("Warning: Program is not Mini-Pascal 2018 compliant: there should be only one block at the top level");
        }
        match block.last() {
            Some(&Statement::Block(_)) => {}
            _ => eprintln!("Warning: Program is not Mini-Pascal 2018 compliant: there should be a block at the end of the program")
        }
    }
    
    // analysoidaan lohkon lauseet (pass 2)
    for stmt in block {
        analyse_stmt(stmt, nt, false);
    }
    nt.pop();
}

// analysoi yhden lauseen
fn analyse_stmt(stmt: &mut Statement, nt: &mut Nametable, is_top: bool) {
    match stmt {
        &mut Statement::Definition(Definition::Function(ref name, ref params, ref return_type, ref mut body)) => {
            check_identifier(name); // tarkistetaan, että nimi ei ole avainsana
            
            // luodaan uusi symbolitaulu ja lisätään siihen näkyvissä olevat funktiot ja proseduurit
            let mut new_nt = Nametable::new(return_type.clone());
            new_nt.push();
            for map in &nt.stack {
                for (name, def) in map {
                    if let Definition::Function(_, _, _, _) = def.clone() {
                        new_nt.peek().insert(name.clone(), def.clone());
                    }
                }
            }
            // lisätään parametrit (sisältää nonlokaalit)
            nt.push();
            for param in &*params {
                new_nt.peek().insert(param.name.clone(), Definition::Variable(param.clone()));
            }
            
            // analysoidaan vartalo
            analyse_stmt(&mut *body.borrow_mut(), &mut new_nt, false);
        }
        &mut Statement::Definition(Definition::Variable(ref par)) => {
            check_identifier(&par.name); // tarkistetaan, että nimi ei ole avainsana
        }
        
        // muille lauseille analysoidaan rekursiivisesti alilauseet ja lausekkeet, sekä tehdään muut tarpeelliset tarkistukset
        &mut Statement::Block(ref mut stmts) => {
            analyse_block(stmts, nt, is_top);
        }
        &mut Statement::Expression(ref mut expr) => {
            analyse_expr(expr, &nt);
        }
        &mut Statement::Return(ref mut expr) => {
            analyse_expr(expr, &nt);
            if !check_types(&expr.etype, &nt.return_type) {
                eprintln!("Semantic error: Type mismatch: incorrect return type: expected {}, got {}", nt.return_type, expr.etype);
                return;
            }
        }
        &mut Statement::SimpleReturn => {
            if !check_types(&Type::Void, &nt.return_type) {
                eprintln!("Semantic error: Type mismatch: incorrect return type: expected {}, got void", nt.return_type);
                return;
            }
        }
        &mut Statement::IfElse(ref mut cond, ref mut then, ref mut otherwise) => {
            analyse_expr(cond, nt);
            if !check_types(&cond.etype, &Type::Boolean) {
                eprintln!("Semantic error: Type mismatch: if condition must be boolean: expected boolean, got {}", cond.etype);
                return;
            }
            analyse_stmt(then, nt, false);
            analyse_stmt(otherwise, nt, false);
        }
        &mut Statement::While(ref mut cond, ref mut body) => {
            analyse_expr(cond, nt);
            if !check_types(&cond.etype, &Type::Boolean) {
                eprintln!("Semantic error: Type mismatch: while condition must be boolean: expected boolean, got {}", cond.etype);
                return;
            }
            analyse_stmt(body, nt, false);
        }
        &mut Statement::Nop => {}
    }
}

// analysoi lausekkeen
fn analyse_expr(expr: &mut ExpressionBox, nt: &Nametable) {
    match &mut *expr.expr {
        // analysoidaan alilausekkeet ja tehdään tarpeelliset tarkistukset:
        &mut Expression::BiOperator(ref op, ref mut a, ref mut b) => {
            analyse_expr(a, nt);
            analyse_expr(b, nt);
            if !check_types(&a.etype, &b.etype) {
                eprintln!("Semantic error: Type mismatch: {} and {} are not compatible", a.etype, b.etype);
                return;
            }
            let allowed_types = op.allowed_types();
            if !allowed_types.contains(&a.etype) {
                eprintln!("Semantic error: Type mismatch: {:?} expected {:?}, got {}", op, allowed_types, a.etype);
            }
        }
        &mut Expression::UnOperator(UnaryOperator::Size, ref mut a) => {
            analyse_expr(a, nt);
            if let Type::Array(_, _) = a.etype {}
            else {
                eprintln!("Semantic error: Type mismatch: Size expected [Array], got {}", a.etype);
            }
        }
        &mut Expression::UnOperator(ref op, ref mut a) => {
            analyse_expr(a, nt);
            let allowed_types = op.allowed_types();
            if !allowed_types.contains(&a.etype) {
                eprintln!("Semantic error: Type mismatch: {:?} expected {:?}, got {}", op, allowed_types, a.etype);
            }
        }
        &mut Expression::Variable(ref name, ref mut reference) => {
            check_identifier(name);
            if let Some(&Definition::Variable(Parameter { is_ref: ref it, .. })) = nt.find_definition(&name) {
                **reference = *it;
            } else {
                eprintln!("Semantic error: {} is not a variable but it is used like one", name);
                return;
            }
        }
        &mut Expression::Index(ref name, ref mut index) => {
            analyse_expr(index, nt);
            if !check_types(&index.etype, &Type::Integer) {
                eprintln!("Semantic error: Type mismatch: index of {} must be integer", name);
                return;
            }
            if let Some(&Definition::Variable(Parameter { vtype: Type::Array(_, _), .. })) = nt.find_definition(&name) {}
            else {
                eprintln!("Semantic error: Type mismatch: {} is indexed but it is not an array", name);
                return;
            }
        }
        &mut Expression::Assign(ref mut var, ref mut val) => {
            analyse_expr(var, nt);
            analyse_expr(val, nt);
            // tarkistetaan, että lval (var) on muuttuja tai taulukkoindeksi
            match &mut *var.expr {
                &mut Expression::Variable(ref name, _) => {
                    if let Some(&Definition::Variable(Parameter { vtype: ref t, .. })) = nt.find_definition(&name) {
                        if !check_types(&val.etype, &t) {
                            eprintln!("Semantic error: Type mismatch: rval (after {} :=) has wrong type: expected {}, got {}", name, t, val.etype);
                            return;
                        }
                    }
                }
                &mut Expression::Index(ref name, _) => {
                    if let Some(&Definition::Variable(Parameter { vtype: Type::Array(ref t, _), .. })) = nt.find_definition(&name) {
                        if !check_types(&val.etype, &t) {
                            eprintln!("Semantic error: Type mismatch: rval has wrong type: expected {}, got {}", t, val.etype);
                            return;
                        }
                    }
                }
                _ => {
                    eprintln!("Semantic error: Left side of assignment is not lval");
                    return;
                }
            }
        }
        &mut Expression::Call(ref name, ref mut mangled_name, ref mut args) => {
            if name != "assert" { // assert on avainsana, mutta sitä saa käyttää funktionimenä funktiota kutsuttaessa
                check_identifier(name);
            }
            for arg in &mut *args {
                analyse_expr(arg, nt);
            }
            if name == "read" {
                for arg in args {
                    arg.make_ref = true;
                }
            }
            else if name == "writeln" {
                // ok
            }
            else if let Some(&Definition::Function(ref new_name, ref params, _, _)) = nt.find_definition(&name) {
                // tarkistetaan argumenttien tyypit
                for (ref mut arg, ref param) in args.iter_mut().zip(params.iter()) {
                    if !check_types(&arg.etype, &param.vtype) {
                        eprintln!("Semantic error: Type mismatch: wrong argument type for param {} of function {}: expected {}, got {}", param.name, name, param.vtype, arg.etype);
                        return;
                    }
                    if param.is_ref {
                         match &mut *arg.expr {
                             &mut Expression::Variable(_, _) => {}
                             &mut Expression::Index(_, _) => {}
                             _ => {
                                 eprintln!("Semantic error: Argument corresponding to a var parameter must be either a variable or an array subscript");
                                 return;
                             }
                         }
                         arg.make_ref = true;
                    }
                }
            
                // lisätään nonlokaalit argumenteiksi
                for i in args.len()..params.len() {
                    if let Some(&Definition::Variable(ref par)) = nt.find_definition(&params[i].name) {
                        let mut new_arg = ExpressionBox::new(Expression::Variable(params[i].name.clone(), Box::new(par.is_ref)));
                        new_arg.etype = params[i].vtype.clone();
                        new_arg.make_ref = true;
                        args.push(new_arg);
                    } else {
                        eprintln!("Semantic error: Wrong number of arguments given for {}", name);
                        return;
                    }
                }
                
                // muutetaan kutsun nimi vastaamaan manglattua nimeä
                *mangled_name = new_name.clone();
            }
        }
        _ => {}
    }
    expr.etype = predict_type(expr, nt);
}

// määrittää lausekkeen tyypin
fn predict_type(expr: &ExpressionBox, nt: &Nametable) -> Type {
    match *expr.expr {
        Expression::Integer(_) => Type::Integer,
        Expression::Real(_) => Type::Real,
        Expression::String(_) => Type::String,
        Expression::BiOperator(BinaryOperator::Add, ref a, _) => a.etype.clone(), // tyyppi on sama kuin operandien tyyppi
        Expression::BiOperator(BinaryOperator::Sub, ref a, _) => a.etype.clone(),
        Expression::BiOperator(BinaryOperator::Mul, ref a, _) => a.etype.clone(),
        Expression::BiOperator(BinaryOperator::Div, ref a, _) => a.etype.clone(),
        Expression::BiOperator(BinaryOperator::Mod, ref a, _) => a.etype.clone(),
        Expression::UnOperator(UnaryOperator::Plus, ref a) => a.etype.clone(),
        Expression::UnOperator(UnaryOperator::Minus, ref a) => a.etype.clone(),
        Expression::UnOperator(UnaryOperator::Size, _) => Type::Integer,
        Expression::BiOperator(BinaryOperator::Lt, _, _) => Type::Boolean,
        Expression::BiOperator(BinaryOperator::Gt, _, _) => Type::Boolean,
        Expression::BiOperator(BinaryOperator::Leq, _, _) => Type::Boolean,
        Expression::BiOperator(BinaryOperator::Geq, _, _) => Type::Boolean,
        Expression::BiOperator(BinaryOperator::Neq, _, _) => Type::Boolean,
        Expression::BiOperator(BinaryOperator::Eq, _, _) => Type::Boolean,
        Expression::BiOperator(BinaryOperator::And, _, _) => Type::Boolean,
        Expression::BiOperator(BinaryOperator::Or, _, _) => Type::Boolean,
        Expression::UnOperator(UnaryOperator::Not, _) => Type::Boolean,
        Expression::Variable(ref name, _) => {
            if let Some(&Definition::Variable(Parameter { vtype: ref t, .. })) = nt.find_definition(&name) {
                t.clone()
            } else {
                eprintln!("Semantic error: Not a variable: {}", name);
                Type::Error
            }
        },
        Expression::Index(ref name, _) => {
            if let Some(&Definition::Variable(Parameter { vtype: Type::Array(ref t, _), .. })) = nt.find_definition(&name) {
                (**t).clone()
            } else {
                eprintln!("Semantic error: Not an array: {}", name);
                Type::Error
            }
        },
        Expression::Call(ref name, _, _) => {
            if ["writeln", "read"].contains(&name.as_str()) {
                Type::Void
            }
            else if let Some(&Definition::Function(_, _, ref t, _)) = nt.find_definition(name) {
                t.clone()
            } else {
                eprintln!("Semantic error: Not a function: {}", name);
                Type::Error
            }
        },
        Expression::Assign(_, ref rexpr) => rexpr.etype.clone()
    }
}

//////////////////////////////////////////////////////////////////////////////
// CODE GENERATION ///////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// muuttaa tyypin C:ksi
impl Type {
    fn to_c(&self, var: &String) -> String {
        match *self {
            Type::Boolean => format!("char {}", var),
            Type::Integer => format!("int {}", var),
            Type::Real => format!("float {}", var),
            Type::String => format!("char *{}", var),
            Type::Array(ref t, _) => t.to_c(&format!("*{}", var)),
            Type::Void => format!("void {}", var),
            Type::Error => format!("unknown {}", var)
        }
    }
}

// muuttaa parametrin tai muuttujan C:ksi (dereferensoi, jos kyseessä on var-parametri)
impl Parameter {
    fn to_c(&self) -> String {
        if self.is_ref {
            self.vtype.to_c(&format!("*{}", self.name))
        } else {
            self.vtype.to_c(&self.name)
        }
    }
}

// muuttaa operaattorin C:ksi
impl BinaryOperator {
    fn to_c(&self) -> String {
        String::from(
            match *self {
                BinaryOperator::Eq => "==",
                BinaryOperator::Neq => "!=",
                BinaryOperator::Lt => "<",
                BinaryOperator::Leq => "<=",
                BinaryOperator::Gt => ">",
                BinaryOperator::Geq => ">=",
                BinaryOperator::Add => "+",
                BinaryOperator::Sub => "-",
                BinaryOperator::Mul => "*",
                BinaryOperator::Div => "/",
                BinaryOperator::Mod => "%",
                BinaryOperator::And => "&&",
                BinaryOperator::Or => "||"
            }
        )
    }
}

// muuttaa operaattorin C:ksi
impl UnaryOperator {
    fn to_c(&self) -> String {
        String::from(
            match *self {
                UnaryOperator::Plus => "+",
                UnaryOperator::Minus => "-",
                UnaryOperator::Not => "!",
                UnaryOperator::Size => "array_len"
            }
        )
    }
}

// sisältää koodigeneraattorin tilan
struct CodeGenerator {
    indent: usize,   // sisennystaso
    var_counter: i8, // laskuri väliaikaismuuttujien nimeämistä varten
    output: String,  // ulostulopuskuri
    header: String,  // headerin ulostulopuskuri
    queue: Vec<Definition> // käsiteltävien funktioiden ja proseduurien jono
}

impl CodeGenerator {
    fn new() -> CodeGenerator {
        CodeGenerator {
            indent: 0,
            var_counter: 0,
            output: String::new(),
            header: String::new(),
            queue: Vec::new()
        }
    }
    
    // luo nimen uudelle väliaikaismuuttujalle tai labelille
    fn new_var(&mut self) -> String {
        self.var_counter += 1;
        format!("tmp{}", self.var_counter)
    }
    
    // lisää rivin ulostulopuskuriin
    fn generate(&mut self, code: String) {
        self.output = format!("{}{}{}\n", self.output, " ".repeat(self.indent), code);
    }
    
    // lisää rivin headerin ulostulopuskuriin
    fn generate_header(&mut self, code: String) {
        self.header = format!("{}{}{}\n", self.header, " ".repeat(self.indent), code);
    }
    
    // lisää str-tyyppisen merkkijonon ulostulopuskuriin
    fn generate_str(&mut self, code: &str) {
        self.generate(String::from(code));
    }
    
    fn generate_def(&mut self, def: Definition) {
        if let Definition::Function(ref name, ref params, ref rtype, ref body) = def {
            let paramcodes: Vec<_> = params.iter().map(|p| p.to_c()).collect();
            let signature = format!("{}", rtype.to_c(&format!("{}({})", name, paramcodes.join(", "))));
            self.generate_header(format!("{};", signature)); // header-rivi
            // varsinainen ulostulo:
            self.generate(format!("{} {{", signature));
            self.indent += 1;
            self.generate_stmt(&*body.borrow_mut());
            self.indent -= 1;
            self.generate_str("}");
        }
        else {
            assert!(false); // globaalit muuttujat käännetään main-funktion sisäisiksi paikallisiksi muuttujiksi, eikä niitä ole globaalilla tasolla C-koodissa
        }
    }

    // kääntää lauseen
    fn generate_stmt(&mut self, stmt: &Statement) {
        match *stmt {
            Statement::Definition(Definition::Variable(ref par)) => {
                self.generate(format!("{};", par.to_c()));
                if let Type::Array(ref t, ref size) = par.vtype { // jos array-tyyppisellä muuttujalla on koko, alustetaan array
                    if *size != -1 {
                        self.generate(format!("{} = make_array({}, {});", par.name, size, t.to_c(&String::new())));
                    }
                }
            }
            Statement::Definition(ref f) /* f on Definition::Function */ => {
                self.queue.push(f.clone());
            }
            Statement::Block(ref stmts) => {
                self.generate_str("{");
                self.indent += 1;
                for stmt in stmts {
                    self.generate_stmt(&stmt);
                }
                self.indent -= 1;
                self.generate_str("}");
            }
            Statement::Expression(ref expr) => {
                self.generate_expr(expr);
            }
            Statement::Return(ref expr) => {
                let var = self.generate_expr(expr);
                self.generate(format!("return {};", var));
            }
            Statement::SimpleReturn => {
                self.generate_str("return;");
            }
            Statement::IfElse(ref cond, ref then, ref otherwise) => {
                let otherwise_label = self.new_var();
                let out_label = self.new_var();
                let condcode = self.generate_expr(cond);
                self.generate(format!("if (!{}) goto {};", condcode, otherwise_label));
                self.generate_stmt(then);
                self.generate(format!("goto {};", out_label));
                self.generate(format!("{}:;", otherwise_label));
                self.generate_stmt(otherwise);
                self.generate(format!("{}:;", out_label));
            }
            Statement::While(ref cond, ref body) => {
                let start_label = self.new_var();
                let out_label = self.new_var();
                self.generate(format!("{}:;", start_label));
                let condcode = self.generate_expr(cond);
                self.generate(format!("if (!{}) goto {};", condcode, out_label));
                self.generate_stmt(body);
                self.generate(format!("goto {};", start_label));
                self.generate(format!("{}:;", out_label));
            }
            Statement::Nop => self.generate_str("/* nop */")
        }
    }
    
    fn generate_expr(&mut self, expr: &ExpressionBox) -> String {
        let etype = expr.etype.clone();
        let make_ref = expr.make_ref;
        match *expr.expr {
            Expression::Integer(ref i) => i.to_string(),
            Expression::Real(ref i) => i.to_string(),
            Expression::String(ref s) => format!("\"{}\"", s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n")),
            Expression::BiOperator(ref op, ref a, ref b) => {
                let tmp = self.new_var();
                let op = op.to_c();
                let acode = self.generate_expr(a);
                let bcode = self.generate_expr(b);
                self.generate(format!("{} = {} {} {};", etype.to_c(&tmp), acode, op, bcode));
                tmp
            }
            Expression::UnOperator(ref op, ref a) => {
                let tmp = self.new_var();
                let op = op.to_c();
                let acode = self.generate_expr(a);
                self.generate(format!("{} = {}({});", etype.to_c(&tmp), op, acode));
                tmp
            }
            Expression::Variable(ref name, ref is_ref) => {
                if make_ref { // jos lauseke on var-parametria vastaava argumentti, lauseke referensoidaan
                    if **is_ref {
                        format!("{}", name)
                    } else {
                        format!("&{}", name)
                    }
                } else { // lauseketta ei referensoida
                    if **is_ref {
                        format!("*{}", name)
                    } else {
                        format!("{}", name)
                    }
                }
            }
            Expression::Index(ref name, ref index) => {
                let icode = self.generate_expr(index);
                // generoidaan tarkistus taulukon koolle
                self.generate(format!("assert(0 <= {} && {} < array_len({}));", icode, icode, name));
                if make_ref { // taulukko referensoidaan, jos se on var-parametria vastaava argumentti
                    format!("&{}[{}]", name, icode)
                } else {
                    format!("{}[{}]", name, icode)
                }
            }
            Expression::Call(ref name, ref mangled_name, ref args) => {
                // sisäänrakennettu read-funktio
                if name == "read" {
                    for arg in args {
                        let argcode = self.generate_expr(arg);
                        match arg.etype {
                            Type::Integer => {
                                self.generate(format!("scanf(\"%d\", {});", argcode));
                            }
                            Type::Real => {
                                self.generate(format!("scanf(\"%f\", {});", argcode));
                            }
                            Type::String => {
                                self.generate(format!("gets_s({}, 256);", argcode));
                            }
                            _ => {}
                        }
                    }
                    String::from("void")
                // sisäänrakennettu writeln-funktio
                } else if name == "writeln" {
                    let mut formatcodes = Vec::new();
                    let mut argcodes = Vec::new();
                    for arg in args {
                        let argcode = self.generate_expr(arg);
                        let mode = match arg.etype {
                            Type::Integer => "%d",
                            Type::Real => "%f",
                            Type::String => "%s",
                            _ => ""
                        };
                        formatcodes.push(mode);
                        argcodes.push(argcode);
                    }
                    self.generate(format!("printf(\"{}\\n\", {});", formatcodes.join(" "), argcodes.join(", ")));
                    String::from("void")
                // tavallinen funktiokutsu
                } else {
                    let mut argcodes = Vec::new();
                    for arg in args {
                        argcodes.push(self.generate_expr(arg));
                    }
                    // luodaan väliaikaismuuttuja palautetulle arvolle vain, jos funktio on funktio eikä proseduuri
                    if etype == Type::Void {
                        self.generate(format!("{}({});", mangled_name, argcodes.join(", ")));
                        String::from("void")
                    } else {
                        let tmp = self.new_var();
                        self.generate(format!("{} = {}({});", etype.to_c(&tmp), mangled_name, argcodes.join(", ")));
                        tmp
                    }
                }
            }
            Expression::Assign(ref lval, ref rval) => {
                let lvalcode = self.generate_expr(lval);
                let rvalcode = self.generate_expr(rval);
                self.generate(format!("{} = {};", lvalcode, rvalcode));
                lvalcode
            }
        }
    }
}
