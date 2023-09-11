use anyhow::{anyhow, Result};
use log::*;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::{char, digit1},
    combinator::{eof, opt},
    multi::many_till,
    sequence::tuple,
    IResult,
};
use std::mem;

use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::emulator::vm::*;
use crate::fixture::Fixture;

//-------------------------------

// A specifier takes the following form:
//    %[$][flags][width][.precision][length modifier]conversion

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
enum Flag {
    LeftJustify,
    Sign,
    Space,
    ZeroPad,
    Alternate,
    Group,
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
enum LengthModifier {
    Short,
    Long,
    LongLong,
    IntMax,
    SizeT,
    PtrDiff,
    LongDouble,
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
enum Conversion {
    SignedInt,
    UnsignedInt,
    Octal,
    HexLower,
    HexUpper,
    Float,
    Char,
    String,
    Pointer,
    Count,
    Percent,
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct FormatSpecifier {
    flag: Option<Flag>,
    width: Option<usize>,
    precision: Option<usize>,
    length_modifier: Option<LengthModifier>,
    conversion: Conversion,
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum Instruction {
    Literal(String),
    Specifier(FormatSpecifier),
}

// Combinator that takes a char and a Flag and returns a parser.
fn flag_char<'a>(c: char, flag: Flag) -> impl Fn(&'a str) -> IResult<&'a str, Flag> {
    move |input: &str| {
        let (input, _) = char(c)(input)?;
        Ok((input, flag))
    }
}

fn flag(input: &str) -> IResult<&str, Flag> {
    alt((
        flag_char('-', Flag::LeftJustify),
        flag_char('+', Flag::Sign),
        flag_char(' ', Flag::Space),
        flag_char('0', Flag::ZeroPad),
        flag_char('#', Flag::Alternate),
        flag_char('\'', Flag::Group),
    ))(input)
}

#[test]
fn test_flag() {
    assert_eq!(flag("-"), Ok(("", Flag::LeftJustify)));
    assert_eq!(flag("+"), Ok(("", Flag::Sign)));
    assert_eq!(flag(" "), Ok(("", Flag::Space)));
    assert_eq!(flag("0"), Ok(("", Flag::ZeroPad)));
    assert_eq!(flag("#"), Ok(("", Flag::Alternate)));
    assert_eq!(flag("'"), Ok(("", Flag::Group)));
}

fn width(input: &str) -> IResult<&str, usize> {
    let (input, width) = digit1(input)?;
    Ok((input, width.parse().unwrap()))
}

#[test]
fn test_width() {
    assert_eq!(width("1"), Ok(("", 1)));
    assert_eq!(width("12"), Ok(("", 12)));
    assert_eq!(width("123"), Ok(("", 123)));
}

fn precision(input: &str) -> IResult<&str, usize> {
    let (input, _) = char('.')(input)?;
    let (input, precision) = digit1(input)?;
    Ok((input, precision.parse().unwrap()))
}

#[test]
fn test_precision() {
    assert_eq!(precision(".1"), Ok(("", 1)));
    assert_eq!(precision(".12"), Ok(("", 12)));
    assert_eq!(precision(".123"), Ok(("", 123)));
}

// Combinator that takes a char and a LengthModifier and returns a parser.
fn length_modifier_tag<'a>(
    lit: &'a str,
    length_modifier: LengthModifier,
) -> impl Fn(&'a str) -> IResult<&'a str, LengthModifier> {
    move |input: &str| {
        let (input, _) = tag(lit)(input)?;
        Ok((input, length_modifier))
    }
}

fn length_modifier(input: &str) -> IResult<&str, LengthModifier> {
    alt((
        length_modifier_tag("h", LengthModifier::Short),
        length_modifier_tag("ll", LengthModifier::LongLong),
        length_modifier_tag("l", LengthModifier::Long),
        length_modifier_tag("j", LengthModifier::IntMax),
        length_modifier_tag("z", LengthModifier::SizeT),
        length_modifier_tag("t", LengthModifier::PtrDiff),
        length_modifier_tag("L", LengthModifier::LongDouble),
    ))(input)
}

#[test]
fn test_length_modifier() {
    assert_eq!(length_modifier("h"), Ok(("", LengthModifier::Short)));
    assert_eq!(length_modifier("l"), Ok(("", LengthModifier::Long)));
    assert_eq!(length_modifier("ll"), Ok(("", LengthModifier::LongLong)));
    assert_eq!(length_modifier("j"), Ok(("", LengthModifier::IntMax)));
    assert_eq!(length_modifier("z"), Ok(("", LengthModifier::SizeT)));
    assert_eq!(length_modifier("t"), Ok(("", LengthModifier::PtrDiff)));
    assert_eq!(length_modifier("L"), Ok(("", LengthModifier::LongDouble)));
}

// Combinator that takes a char and a Conversion and returns a parser.
fn conversion_char<'a>(
    c: char,
    conversion: Conversion,
) -> impl Fn(&'a str) -> IResult<&'a str, Conversion> {
    move |input: &str| {
        let (input, _) = char(c)(input)?;
        Ok((input, conversion))
    }
}

fn conversion(input: &str) -> IResult<&str, Conversion> {
    alt((
        conversion_char('d', Conversion::SignedInt),
        conversion_char('i', Conversion::SignedInt),
        conversion_char('u', Conversion::UnsignedInt),
        conversion_char('o', Conversion::Octal),
        conversion_char('x', Conversion::HexLower),
        conversion_char('X', Conversion::HexUpper),
        conversion_char('f', Conversion::Float),
        conversion_char('F', Conversion::Float),
        conversion_char('e', Conversion::Float),
        conversion_char('E', Conversion::Float),
        conversion_char('g', Conversion::Float),
        conversion_char('G', Conversion::Float),
        conversion_char('a', Conversion::Float),
        conversion_char('A', Conversion::Float),
        conversion_char('c', Conversion::Char),
        conversion_char('s', Conversion::String),
        conversion_char('p', Conversion::Pointer),
        conversion_char('n', Conversion::Count),
        conversion_char('%', Conversion::Percent),
    ))(input)
}

#[test]
fn test_conversion() {
    assert_eq!(conversion("d"), Ok(("", Conversion::SignedInt)));
    assert_eq!(conversion("i"), Ok(("", Conversion::SignedInt)));
    assert_eq!(conversion("u"), Ok(("", Conversion::UnsignedInt)));
    assert_eq!(conversion("o"), Ok(("", Conversion::Octal)));
    assert_eq!(conversion("x"), Ok(("", Conversion::HexLower)));
    assert_eq!(conversion("X"), Ok(("", Conversion::HexUpper)));
    assert_eq!(conversion("f"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("F"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("e"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("E"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("g"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("G"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("a"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("A"), Ok(("", Conversion::Float)));
    assert_eq!(conversion("c"), Ok(("", Conversion::Char)));
    assert_eq!(conversion("s"), Ok(("", Conversion::String)));
    assert_eq!(conversion("p"), Ok(("", Conversion::Pointer)));
    assert_eq!(conversion("n"), Ok(("", Conversion::Count)));
    assert_eq!(conversion("%"), Ok(("", Conversion::Percent)));
}

// Parses the specifier portion of a format string.
fn specifier(input: &str) -> IResult<&str, Instruction> {
    let (input, _) = tag("%")(input)?; // Consume the '%'
    let (input, (flag, width, precision, length_modifier, conversion)) = tuple((
        opt(flag),
        opt(width),
        opt(precision),
        opt(length_modifier),
        conversion,
    ))(input)?;
    Ok((
        input,
        Instruction::Specifier(FormatSpecifier {
            flag,
            width,
            precision,
            length_modifier,
            conversion,
        }),
    ))
}

#[test]
fn test_specifier() {
    assert_eq!(
        specifier("%llu"),
        Ok((
            "",
            Instruction::Specifier(FormatSpecifier {
                flag: None,
                width: None,
                precision: None,
                length_modifier: Some(LengthModifier::LongLong),
                conversion: Conversion::UnsignedInt,
            })
        ))
    );
}

// A literal is a string of characters that are not format specifiers.  (ie. do not begin with '%')
fn literal(input: &str) -> IResult<&str, Instruction> {
    let (input, literal) = take_till(|c| c == '%')(input)?;
    Ok((input, Instruction::Literal(literal.to_string())))
}

#[test]
fn test_literal() {
    assert_eq!(
        literal("Hello, %llu world!"),
        Ok(("%llu world!", Instruction::Literal("Hello, ".to_string())))
    );
    assert_eq!(
        literal("Hello, world!"),
        Ok(("", Instruction::Literal("Hello, world!".to_string())))
    );
}

fn instruction(input: &str) -> IResult<&str, Instruction> {
    alt((specifier, literal))(input)
}

#[test]
fn test_instruction() {
    assert_eq!(
        instruction("Hello, %llu world!"),
        Ok(("%llu world!", Instruction::Literal("Hello, ".to_string())))
    );
    assert_eq!(
        instruction("%llu foo"),
        Ok((
            " foo",
            Instruction::Specifier(FormatSpecifier {
                flag: None,
                width: None,
                precision: None,
                length_modifier: Some(LengthModifier::LongLong),
                conversion: Conversion::UnsignedInt,
            })
        ))
    );
}

fn format_string(input: &str) -> IResult<&str, Vec<Instruction>> {
    let (input, (instrs, _)) = many_till(instruction, eof)(input)?;
    Ok((input, instrs))
}

#[test]
fn test_format_string() {
    assert_eq!(
        format_string("Hello, %llu world!"),
        Ok((
            "",
            vec![
                Instruction::Literal("Hello, ".to_string()),
                Instruction::Specifier(FormatSpecifier {
                    flag: None,
                    width: None,
                    precision: None,
                    length_modifier: Some(LengthModifier::LongLong),
                    conversion: Conversion::UnsignedInt,
                }),
                Instruction::Literal(" world!".to_string()),
            ]
        ))
    );
}

// Parses a format string into a vector of Instructions.
fn parse_format_string(input: &str) -> Result<Vec<Instruction>> {
    let r = format_string(input);
    match r {
        Ok((_, instructions)) => Ok(instructions),
        Err(e) => Err(anyhow!("Failed to parse format string: {}", e)),
    }
}

#[test]
fn test_parse_format_string() {
    assert_eq!(
        parse_format_string("nr_entries = %llu!").unwrap(),
        vec![
            Instruction::Literal("nr_entries = ".to_string()),
            Instruction::Specifier(FormatSpecifier {
                flag: None,
                width: None,
                precision: None,
                length_modifier: Some(LengthModifier::LongLong),
                conversion: Conversion::UnsignedInt,
            }),
            Instruction::Literal("!".to_string()),
        ]
    );
}

//-------------------------------

fn arg_to_reg(arg: usize) -> Reg {
    Reg::from(Reg::A0 as u32 + arg as u32)
}

fn exec_specifier(spec: &FormatSpecifier, vm: &VM, arg_index: usize) -> Result<String> {
    let reg = arg_to_reg(arg_index);
    let value = vm.reg(reg);

    let mut result = String::new();
    match spec.conversion {
        Conversion::SignedInt => {
            result.push_str(&format!("{}", value as i64));
        }
        Conversion::UnsignedInt => {
            result.push_str(&format!("{}", value));
        }
        Conversion::Octal => {
            result.push_str(&format!("{:o}", value));
        }
        Conversion::HexLower => {
            result.push_str(&format!("{:x}", value));
        }
        Conversion::HexUpper => {
            result.push_str(&format!("{:X}", value));
        }
        Conversion::Float => {
            let value = unsafe { mem::transmute::<u64, f64>(value) };
            result.push_str(&format!("{}", value));
        }
        Conversion::Char => {
            let value = unsafe { mem::transmute::<u32, char>(value as u32) };
            result.push_str(&format!("{}", value));
        }
        Conversion::String => {
            result = vm.mem.read_string(Addr(value))?;
        }
        Conversion::Pointer => {
            result.push_str(&format!("0x{:x}", value));
        }
        Conversion::Count => {
            result.push_str(&format!("{}", value));
        }
        Conversion::Percent => {
            result.push_str(&format!("%{}", value));
        }
    }
    Ok(result)
}

fn exec_instruction(instr: &Instruction, vm: &VM, arg_index: usize) -> Result<String> {
    match instr {
        Instruction::Literal(literal) => Ok(literal.to_string()),
        Instruction::Specifier(specifier) => exec_specifier(specifier, vm, arg_index),
    }
}

fn exec_instructions(instructions: &[Instruction], vm: &VM) -> Result<String> {
    let mut result = String::new();
    let mut arg_index = 1; // format string was at A0
    for instr in instructions {
        result.push_str(&exec_instruction(instr, vm, arg_index)?);
        if let Instruction::Specifier(_) = instr {
            arg_index += 1;
        }
    }
    Ok(result)
}

fn do_printk(vm: &VM) -> Result<String> {
    let format_string = vm.mem.read_string(Addr(vm.reg(Reg::A0)))?;

    // FIXME: First 2 chars contain the severity level, which we ignore for now.
    let instructions = parse_format_string(&format_string[2..])?;
    exec_instructions(&instructions, vm)
}

// Trim trailing whitespace from a string.
fn trim_trailing(s: &str) -> String {
    let mut result = String::new();
    let chars = s.chars().rev();
    let mut found_non_whitespace = false;
    for c in chars {
        if c.is_whitespace() && !found_non_whitespace {
            continue;
        }
        found_non_whitespace = true;
        result.push(c);
    }
    result.chars().rev().collect()
}

pub fn printk(fix: &mut Fixture) -> Result<()> {
    info!("{}", trim_trailing(&do_printk(&fix.vm)?));
    fix.vm.ret(0);
    Ok(())
}
