use nom::branch::alt;
use nom::bytes::complete::{is_a, tag, take_while1};
use nom::character::complete::{alpha0, hex_digit1, multispace0};
use nom::combinator::eof;
use nom::multi::{many1, many_till, separated_list0};
use nom::sequence::{delimited, preceded, Tuple};

pub struct Program {
    pub instructions: Vec<Instruction>,
}

#[derive(strum::EnumString, Debug, PartialEq)]
pub enum Operator {
    AND,
    ASL,
    BCC,
    BCS,
    BEQ,
    BIT,
    BMI,
    BNE,
    BPL,
    BRK,
    BVC,
    BVS,
    CLC,
    CLD,
    CLI,
    CLV,
    CMP,
    CPX,
    CPY,
    DEC,
    DEX,
    DEY,
    EOR,
    INC,
    INX,
    INY,
    JMP,
    JSR,
    LDA,
    LDX,
    LDY,
    LSR,
    NOP,
    ORA,
    PHA,
    PHP,
    PLA,
    PLP,
    ROL,
    ROR,
    RTI,
    RTS,
    SBC,
    SEC,
    SED,
    SEI,
    STA,
    STX,
    STY,
    TAX,
    TAY,
    TSX,
    TXA,
    TXS,
    TYA,
}

#[derive(Debug, PartialEq)]
pub enum Operand {
    X,
    Y,
    ImmediateValue(Value),
    Value(Value),
    Paren(Vec<Operand>),
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Word(u8),
    DoubleWord(u16),
    Label(String),
}

#[derive(Debug, PartialEq)]
pub struct Instruction {
    pub operator: Operator,
    pub operands: Vec<Operand>,
}

type ParserResult<'a, O = Instruction> = nom::IResult<&'a str, O>;

/// parse 6502 ASM code
pub fn parse(code: &str) -> ParserResult<Program> {
    // TODO: parsing comments
    let (remain, (instructions, _)) = many_till(parse_instruction, eof)(code)?;
    let program = Program { instructions };
    Ok((remain, program))
}

fn parse_instruction(code: &str) -> ParserResult {
    let (code, operator) = parse_operator(code)?;
    let (code, operands) = parse_operands(code)?;
    Ok((code, Instruction { operator, operands }))
}

fn parse_operator(code: &str) -> ParserResult<Operator> {
    let (code, _) = multispace0(code)?;
    let (code, operator) = alpha0(code)?;
    let operator = Operator::try_from(operator).map_err(|_e| nom::Err::Error(nom::error::make_error(operator, nom::error::ErrorKind::Fail)))?;
    Ok((code, operator))
}

fn parse_operands(code: &str) -> ParserResult<Vec<Operand>> {
    let (code, _) = multispace0(code)?;
    separated_list0(tag(","), parse_operand)(code)
}

fn parse_operand(code: &str) -> ParserResult<Operand> {
    let (code, (_, operand)) = (
        multispace0,
        alt((
            parse_x_or_y,
            parse_immediate_operand,
            parse_value_operand,
            parse_paren,
        )),
    ).parse(code)?;
    Ok((code, operand))
}

fn parse_immediate_operand(code: &str) -> ParserResult<Operand> {
    let (code, _) = multispace0(code)?;
    let (remain, value) = preceded(tag("#"), parse_value)(code)?;
    Ok((remain, Operand::ImmediateValue(value)))
}

fn parse_value_operand(code: &str) -> ParserResult<Operand> {
    let (remain, value) = parse_value(code)?;
    Ok((remain, Operand::Value(value)))
}

fn parse_value(code: &str) -> ParserResult<Value> {
    let (code, _) = multispace0(code)?;
    let (remain, value) = alt((
        parse_double_word,
        parse_word,
        parse_label,
    ))(code)?;
    Ok((remain, value))
}

fn parse_double_word(code: &str) -> ParserResult<Value> {
    let (remain, _) = tag("$")(code)?;
    let (remain, digit) = hex_digit1(remain)?;
    if digit.len() != 4 {
        return Err(nom::Err::Error(nom::error::make_error(digit, nom::error::ErrorKind::Digit)));
    }
    let digit = u16::from_str_radix(digit, 16).map_err(|_| nom::Err::Failure(nom::error::make_error(digit, nom::error::ErrorKind::Digit)))?;
    Ok((remain, Value::DoubleWord(digit)))
}

fn parse_word(code: &str) -> ParserResult<Value> {
    let (remain, _) = tag("$")(code)?;
    let (remain, digit) = hex_digit1(remain)?;
    if digit.len() != 2 {
        return Err(nom::Err::Error(nom::error::make_error(digit, nom::error::ErrorKind::Digit)));
    }
    let digit = u8::from_str_radix(digit, 16).map_err(|_| nom::Err::Failure(nom::error::make_error(digit, nom::error::ErrorKind::Digit)))?;
    Ok((remain, Value::Word(digit)))
}

fn parse_label(code: &str) -> ParserResult<Value> {
    let (remain, label) = take_while1(|c: char| {
        c.is_ascii_alphanumeric() || matches!(c, '_')
    })(code)?;
    Ok((remain, Value::Label(label.to_string())))
}

fn parse_x_or_y(code: &str) -> ParserResult<Operand> {
    let (remain, identifier) = is_a("XY")(code)?;
    let operand = match identifier {
        "X" => Operand::X,
        "Y" => Operand::Y,
        _ => unreachable!(),
    };
    Ok((remain, operand))
}

fn parse_paren(code: &str) -> ParserResult<Operand> {
    let (code, operands) = delimited(tag("("), many1(parse_operand), tag(")"))(code)?;
    Ok((code, Operand::Paren(operands)))
}

#[cfg(test)]
mod tests {
    use crate::asm::{Instruction, Operand, Operator, parse, parse_immediate_operand, parse_instruction, parse_operand, parse_operands, parse_operator, parse_x_or_y, Value};

    #[test]
    fn test_parse_immediate_value() {
        assert_eq!(parse_immediate_operand("#$AB"), Ok(("", Operand::ImmediateValue(Value::Word(0xAB)))));
        assert_eq!(parse_immediate_operand("#$00"), Ok(("", Operand::ImmediateValue(Value::Word(0x00)))));
        assert_eq!(parse_immediate_operand("#$12"), Ok(("", Operand::ImmediateValue(Value::Word(0x12)))));

        assert_eq!(parse_immediate_operand("#$ABAB"), Ok(("", Operand::ImmediateValue(Value::DoubleWord(0xABAB)))));
        assert_eq!(parse_immediate_operand("#$0000"), Ok(("", Operand::ImmediateValue(Value::DoubleWord(0x0000)))));
        assert_eq!(parse_immediate_operand("#$1234"), Ok(("", Operand::ImmediateValue(Value::DoubleWord(0x1234)))));

        assert_eq!(parse_immediate_operand("#LIMIT"), Ok(("", Operand::ImmediateValue(Value::Label(String::from("LIMIT"))))));
        assert_eq!(parse_immediate_operand("#ABC_def_1"), Ok(("", Operand::ImmediateValue(Value::Label(String::from("ABC_def_1"))))));
        assert_eq!(parse_immediate_operand("#_hello000"), Ok(("", Operand::ImmediateValue(Value::Label(String::from("_hello000"))))));
        assert_eq!(parse_immediate_operand("#123_world"), Ok(("", Operand::ImmediateValue(Value::Label(String::from("123_world"))))));
    }

    #[test]
    fn test_parse_operand() {
        assert_eq!(parse_operand("$AB"), Ok(("", Operand::Value(Value::Word(0xAB)))));
        assert_eq!(parse_operand("#$AB"), Ok(("", Operand::ImmediateValue(Value::Word(0xAB)))));
        assert_eq!(parse_operand("#Hello"), Ok(("", Operand::ImmediateValue(Value::Label(String::from("Hello"))))));
        assert_eq!(parse_operand("Hello"), Ok(("", Operand::Value(Value::Label(String::from("Hello"))))));
    }

    #[test]
    fn test_parse_x_y() {
        assert_eq!(parse_x_or_y("X"), Ok(("", Operand::X)));
        assert_eq!(parse_x_or_y("Y"), Ok(("", Operand::Y)));
    }

    #[test]
    fn test_parse_operands() {
        assert_eq!(parse_operands("#$12,X"), Ok(("", vec![Operand::ImmediateValue(Value::Word(0x12)), Operand::X])));
        assert_eq!(parse_operands("#Hello,X"), Ok(("", vec![Operand::ImmediateValue(Value::Label(String::from("Hello"))), Operand::X])));
        assert_eq!(parse_operands("$FFFF,X"), Ok(("", vec![Operand::Value(Value::DoubleWord(0xFFFF)), Operand::X])));
    }

    #[test]
    fn test_operator() {
        assert_eq!(parse_operator("JMP"), Ok(("", Operator::JMP)));
        assert_eq!(parse_operator("AND"), Ok(("", Operator::AND)));
        assert_eq!(parse_operator("LDA"), Ok(("", Operator::LDA)));
    }

    #[test]
    fn test_parse_instruction() {
        assert_eq!(parse_instruction("JMP #$1234"), Ok(("", Instruction { operator: Operator::JMP, operands: vec![Operand::ImmediateValue(Value::DoubleWord(0x1234))] })));
        assert_eq!(parse_instruction("   JMP   #$1234"), Ok(("", Instruction { operator: Operator::JMP, operands: vec![Operand::ImmediateValue(Value::DoubleWord(0x1234))] })));
    }

    #[test]
    fn test_parse_program() {
        let (_, program) = parse("LDA #$AB\
JMP $1234,X").unwrap();
        assert_eq!(program.instructions, vec![
            Instruction { operator: Operator::LDA, operands: vec![Operand::ImmediateValue(Value::Word(0xAB))] },
            Instruction { operator: Operator::JMP, operands: vec![Operand::Value(Value::DoubleWord(0x1234)), Operand::X] },
        ]);
    }
}
