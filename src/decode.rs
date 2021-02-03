use std::fmt;

//-------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Reg {
    Zero = 0,
    Ra,
    Sp,
    Gp,
    Tp,
    T0,
    T1,
    T2,
    S0,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
    PC,
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Reg::*;
        match self {
            Zero => write!(f, "zero"),
            Ra => write!(f, "ra"),
            Sp => write!(f, "sp"),
            Gp => write!(f, "gp"),
            Tp => write!(f, "tp"),
            T0 => write!(f, "t0"),
            T1 => write!(f, "t1"),
            T2 => write!(f, "t2"),
            S0 => write!(f, "s0"),
            S1 => write!(f, "s1"),
            A0 => write!(f, "a0"),
            A1 => write!(f, "a1"),
            A2 => write!(f, "a2"),
            A3 => write!(f, "a3"),
            A4 => write!(f, "a4"),
            A5 => write!(f, "a5"),
            A6 => write!(f, "a6"),
            A7 => write!(f, "a7"),
            S2 => write!(f, "s2"),
            S3 => write!(f, "s3"),
            S4 => write!(f, "s4"),
            S5 => write!(f, "s5"),
            S6 => write!(f, "s6"),
            S7 => write!(f, "s7"),
            S8 => write!(f, "s8"),
            S9 => write!(f, "s9"),
            S10 => write!(f, "s10"),
            S11 => write!(f, "s11"),
            T3 => write!(f, "t3"),
            T4 => write!(f, "t4"),
            T5 => write!(f, "t5"),
            T6 => write!(f, "t6"),
            PC => write!(f, "pc"),
        }
    }
}

impl From<u32> for Reg {
    fn from(v: u32) -> Self {
        assert!(v < 33);
        unsafe { core::ptr::read_unaligned(&(v as usize) as *const usize as *const Reg) }
    }
}

/// Extracts the register from an instruction, pass in the first/lowest
/// bit of the register field.
fn reg_at(inst: u32, bit: usize) -> Reg {
    Reg::from((inst >> bit) & 0b11111)
}

/// Extracts a register from a _compressed_ bit field. pass in the first/lowest
/// bit of the field.
fn creg_at(bits: u16, bit: usize) -> Reg {
    Reg::from((((bits >> bit) & 0b111) + 8) as u32)
}

/// Sign extends a given number of bits.
fn sign_extend(x: i32, nbits: u32) -> i32 {
    let n = std::mem::size_of_val(&x) as u32 * 8 - nbits - 1;
    x.wrapping_shl(n).wrapping_shr(n)
}

#[derive(Debug)]
pub enum Inst {
    LUI { rd: Reg, imm: i32 },
    AUIPC { rd: Reg, imm: i32 },

    JAL { rd: Reg, imm: i32 },
    JALR { rd: Reg, rs: Reg, imm: i32 },

    BEQ { rs1: Reg, rs2: Reg, imm: i32 },
    BNE { rs1: Reg, rs2: Reg, imm: i32 },
    BLT { rs1: Reg, rs2: Reg, imm: i32 },
    BGE { rs1: Reg, rs2: Reg, imm: i32 },
    BLTU { rs1: Reg, rs2: Reg, imm: i32 },
    BGEU { rs1: Reg, rs2: Reg, imm: i32 },

    LB { rd: Reg, rs: Reg, imm: i32 },
    LH { rd: Reg, rs: Reg, imm: i32 },
    LW { rd: Reg, rs: Reg, imm: i32 },
    LWU { rd: Reg, rs: Reg, imm: i32 },
    LD { rd: Reg, rs: Reg, imm: i32 },

    LBU { rd: Reg, rs: Reg, imm: i32 },
    LHU { rd: Reg, rs: Reg, imm: i32 },

    SB { rs1: Reg, rs2: Reg, imm: i32 },
    SH { rs1: Reg, rs2: Reg, imm: i32 },
    SW { rs1: Reg, rs2: Reg, imm: i32 },
    SD { rs1: Reg, rs2: Reg, imm: i32 },

    ADDI { rd: Reg, rs: Reg, imm: i32 },
    ADDIW { rd: Reg, rs: Reg, imm: i32 },
    SLTI { rd: Reg, rs: Reg, imm: i32 },
    SLTIU { rd: Reg, rs: Reg, imm: i32 },
    XORI { rd: Reg, rs: Reg, imm: i32 },
    ORI { rd: Reg, rs: Reg, imm: i32 },
    ANDI { rd: Reg, rs: Reg, imm: i32 },
    SLLI { rd: Reg, rs: Reg, shamt: i32 },
    SLLIW { rd: Reg, rs: Reg, shamt: u32 },
    SRLI { rd: Reg, rs: Reg, shamt: u32 },
    SRLIW { rd: Reg, rs: Reg, shamt: u32 },
    SRAIW { rd: Reg, rs: Reg, shamt: u32 },
    SRAI { rd: Reg, rs: Reg, shamt: u32 },

    ADD { rd: Reg, rs1: Reg, rs2: Reg },
    ADDW { rd: Reg, rs1: Reg, rs2: Reg },
    SUB { rd: Reg, rs1: Reg, rs2: Reg },
    SUBW { rd: Reg, rs1: Reg, rs2: Reg },
    SLL { rd: Reg, rs1: Reg, rs2: Reg },
    SLLW { rd: Reg, rs1: Reg, rs2: Reg },
    SRLW { rd: Reg, rs1: Reg, rs2: Reg },
    SRAW { rd: Reg, rs1: Reg, rs2: Reg },
    SLT { rd: Reg, rs1: Reg, rs2: Reg },
    SLTU { rd: Reg, rs1: Reg, rs2: Reg },

    XOR { rd: Reg, rs1: Reg, rs2: Reg },
    SRL { rd: Reg, rs1: Reg, rs2: Reg },
    SRA { rd: Reg, rs1: Reg, rs2: Reg },
    OR { rd: Reg, rs1: Reg, rs2: Reg },
    AND { rd: Reg, rs1: Reg, rs2: Reg },

    // mul
    MUL { rd: Reg, rs1: Reg, rs2: Reg },
    MULH { rd: Reg, rs1: Reg, rs2: Reg },
    MULHSU { rd: Reg, rs1: Reg, rs2: Reg },
    MULHU { rd: Reg, rs1: Reg, rs2: Reg },
    MULW { rd: Reg, rs1: Reg, rs2: Reg },
    DIV { rd: Reg, rs1: Reg, rs2: Reg },
    DIVU { rd: Reg, rs1: Reg, rs2: Reg },
    DIVW { rd: Reg, rs1: Reg, rs2: Reg },
    DIVUW { rd: Reg, rs1: Reg, rs2: Reg },
    REM { rd: Reg, rs1: Reg, rs2: Reg },
    REMU { rd: Reg, rs1: Reg, rs2: Reg },
    REMW { rd: Reg, rs1: Reg, rs2: Reg },
    REMUW { rd: Reg, rs1: Reg, rs2: Reg },

    FENCE,
    FENCEI,

    ECALL,
    EBREAK,

    // atomics
    LRW { rd: Reg, rs: Reg },
    SCW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOSWAPW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOADDW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOXORW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOANDW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOORW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMINW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMAXW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMINUW { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMAXUW { rd: Reg, rs1: Reg, rs2: Reg },
    LRD { rd: Reg, rs: Reg },
    SCD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOSWAPD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOADDD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOXORD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOANDD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOORD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMIND { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMAXD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMINUD { rd: Reg, rs1: Reg, rs2: Reg },
    AMOMAXUD { rd: Reg, rs1: Reg, rs2: Reg },
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Inst::*;
        use Reg::*;

        match self {
            LUI { rd, imm } => write!(f, "lui\t{},0x{:x}", rd, imm),
            AUIPC { rd, imm } => write!(f, "auipc\t{},0x{:x}", rd, imm),

            JAL { rd, imm } => write!(f, "jal\t{},0x{:x}", rd, imm),
            JALR { rd, rs, imm } => {
                if *rd == Zero && *rs == Ra && *imm == 0 {
                    write!(f, "ret")
                } else {
                    write!(f, "jalr\t{},{},0x{:x}", rd, rs, imm)
                }
            }

            BEQ { rs1, rs2, imm } => {
                if *rs2 == Zero {
                    write!(f, "beqz\t{},{}", rs1, imm)
                } else {
                    write!(f, "beq\t{},{},{}", rs1, rs2, imm)
                }
            }
            BNE { rs1, rs2, imm } => write!(f, "bne\t{},{},{}", rs1, rs2, imm),
            BLT { rs1, rs2, imm } => write!(f, "blt\t{},{},{}", rs1, rs2, imm),
            BGE { rs1, rs2, imm } => write!(f, "bge\t{},{},{}", rs1, rs2, imm),
            BLTU { rs1, rs2, imm } => write!(f, "bltu\t{},{},{}", rs1, rs2, imm),
            BGEU { rs1, rs2, imm } => write!(f, "bgeu\t{},{},{}", rs1, rs2, imm),

            LB { rd, rs, imm } => write!(f, "lb\t{},{}({})", rd, imm, rs),
            LH { rd, rs, imm } => write!(f, "lh\t{},{}({})", rd, imm, rs),
            LW { rd, rs, imm } => write!(f, "lw\t{},{}({})", rd, imm, rs),
            LWU { rd, rs, imm } => write!(f, "lwu\t{},{}({})", rd, imm, rs),
            LD { rd, rs, imm } => write!(f, "ld\t{},{}({})", rd, imm, rs),

            LBU { rd, rs, imm } => write!(f, "lbu\t{},{}({})", rd, imm, rs),
            LHU { rd, rs, imm } => write!(f, "lhu\t{},{}({})", rd, imm, rs),

            SB { rs1, rs2, imm } => write!(f, "sb\t{},{}({})", rs2, imm, rs1),
            SH { rs1, rs2, imm } => write!(f, "sh\t{},{}({})", rs2, imm, rs1),
            SW { rs1, rs2, imm } => write!(f, "sw\t{},{}({})", rs2, imm, rs1),
            SD { rs1, rs2, imm } => write!(f, "sd\t{},{}({})", rs2, imm, rs1),

            ADDI { rd, rs, imm } => {
                if *rs == Zero {
                    write!(f, "li\t{},{}", rd, imm)
                } else {
                    write!(f, "addi\t{},{},{}", rd, rs, imm)
                }
            }
            ADDIW { rd, rs, imm } => write!(f, "addiw\t{},{},{}", rd, rs, imm),
            SLTI { rd, rs, imm } => write!(f, "slti\t{},{},{}", rd, rs, imm),
            SLTIU { rd, rs, imm } => write!(f, "sltiu\t{},{},{}", rd, rs, imm),
            XORI { rd, rs, imm } => write!(f, "xori\t{},{},{}", rd, rs, imm),
            ORI { rd, rs, imm } => write!(f, "ori\t{},{},{}", rd, rs, imm),
            ANDI { rd, rs, imm } => write!(f, "andi\t{},{},{}", rd, rs, imm),
            SLLI { rd, rs, shamt } => write!(f, "slli\t{},{},{}", rd, rs, shamt),
            SLLIW { rd, rs, shamt } => write!(f, "slliw\t{},{},{}", rd, rs, shamt),
            SRLI { rd, rs, shamt } => write!(f, "srli\t{},{},{}", rd, rs, shamt),
            SRLIW { rd, rs, shamt } => write!(f, "srliw\t{},{},{}", rd, rs, shamt),
            SRAIW { rd, rs, shamt } => write!(f, "sraiw\t{},{},{}", rd, rs, shamt),
            SRAI { rd, rs, shamt } => write!(f, "srai\t{},{},{}", rd, rs, shamt),

            ADD { rd, rs1, rs2 } => {
                if *rs1 == Zero {
                    write!(f, "mv\t{},{}", rd, rs2)
                } else {
                    write!(f, "add\t{},{},{}", rd, rs1, rs2)
                }
            }
            ADDW { rd, rs1, rs2 } => write!(f, "addw\t{},{},{}", rd, rs1, rs2),
            SUB { rd, rs1, rs2 } => write!(f, "sub\t{},{},{}", rd, rs1, rs2),
            SUBW { rd, rs1, rs2 } => write!(f, "subw\t{},{},{}", rd, rs1, rs2),
            SLL { rd, rs1, rs2 } => write!(f, "sll\t{},{},{}", rd, rs1, rs2),
            SLLW { rd, rs1, rs2 } => write!(f, "sllw\t{},{},{}", rd, rs1, rs2),
            SRLW { rd, rs1, rs2 } => write!(f, "srlw\t{},{},{}", rd, rs1, rs2),
            SRAW { rd, rs1, rs2 } => write!(f, "sraw\t{},{},{}", rd, rs1, rs2),
            SLT { rd, rs1, rs2 } => write!(f, "slt\t{},{},{}", rd, rs1, rs2),
            SLTU { rd, rs1, rs2 } => write!(f, "sltu\t{},{},{}", rd, rs1, rs2),

            XOR { rd, rs1, rs2 } => write!(f, "xor\t{},{},{}", rd, rs1, rs2),
            SRL { rd, rs1, rs2 } => write!(f, "srl\t{},{},{}", rd, rs1, rs2),
            SRA { rd, rs1, rs2 } => write!(f, "sra\t{},{},{}", rd, rs1, rs2),
            OR { rd, rs1, rs2 } => write!(f, "or\t{},{},{}", rd, rs1, rs2),
            AND { rd, rs1, rs2 } => write!(f, "and\t{},{},{}", rd, rs1, rs2),

            MUL { rd, rs1, rs2 } => write!(f, "mul\t{},{},{}", rd, rs1, rs2),
            MULH { rd, rs1, rs2 } => write!(f, "mulh\t{},{},{}", rd, rs1, rs2),
            MULHSU { rd, rs1, rs2 } => write!(f, "mulhsu\t{},{},{}", rd, rs1, rs2),
            MULHU { rd, rs1, rs2 } => write!(f, "mulhu\t{},{},{}", rd, rs1, rs2),
            MULW { rd, rs1, rs2 } => write!(f, "mulw\t{},{},{}", rd, rs1, rs2),
            DIV { rd, rs1, rs2 } => write!(f, "div\t{},{},{}", rd, rs1, rs2),
            DIVU { rd, rs1, rs2 } => write!(f, "divu\t{},{},{}", rd, rs1, rs2),
            DIVW { rd, rs1, rs2 } => write!(f, "divw\t{},{},{}", rd, rs1, rs2),
            DIVUW { rd, rs1, rs2 } => write!(f, "divuw\t{},{},{}", rd, rs1, rs2),
            REM { rd, rs1, rs2 } => write!(f, "rem\t{},{},{}", rd, rs1, rs2),
            REMU { rd, rs1, rs2 } => write!(f, "remu\t{},{},{}", rd, rs1, rs2),
            REMW { rd, rs1, rs2 } => write!(f, "remw\t{},{},{}", rd, rs1, rs2),
            REMUW { rd, rs1, rs2 } => write!(f, "remuw\t{},{},{}", rd, rs1, rs2),

            FENCE => write!(f, "fence"),
            FENCEI => write!(f, "fence_i"),

            ECALL => write!(f, "ecall"),
            EBREAK => write!(f, "ebreak"),

            LRW { rd, rs } => write!(f, "lr.w {},{}", rd, rs),
            SCW { rd, rs1, rs2 } => write!(f, "sc.w {},{},({})", rd, rs1, rs2),
            AMOSWAPW { rd, rs1, rs2 } => write!(f, "amoswap.w {},{},({})", rd, rs1, rs2),
            AMOADDW { rd, rs1, rs2 } => write!(f, "amoadd.w {},{},({})", rd, rs1, rs2),
            AMOXORW { rd, rs1, rs2 } => write!(f, "amoxor.w {},{},({})", rd, rs1, rs2),
            AMOANDW { rd, rs1, rs2 } => write!(f, "amoand.w {},{},({})", rd, rs1, rs2),
            AMOORW { rd, rs1, rs2 } => write!(f, "amoor.w {},{},({})", rd, rs1, rs2),
            AMOMINW { rd, rs1, rs2 } => write!(f, "amomin.w {},{},({})", rd, rs1, rs2),
            AMOMAXW { rd, rs1, rs2 } => write!(f, "amomax.w {},{},({})", rd, rs1, rs2),
            AMOMINUW { rd, rs1, rs2 } => write!(f, "amominu.w {},{},({})", rd, rs1, rs2),
            AMOMAXUW { rd, rs1, rs2 } => write!(f, "amomaxu.w {},{},({})", rd, rs1, rs2),
            LRD { rd, rs } => write!(f, "lr.d {},{}", rd, rs),
            SCD { rd, rs1, rs2 } => write!(f, "sc.d {},{},({})", rd, rs1, rs2),
            AMOSWAPD { rd, rs1, rs2 } => write!(f, "amoswap.d {},{},({})", rd, rs1, rs2),
            AMOADDD { rd, rs1, rs2 } => write!(f, "amoadd.d {},{},({})", rd, rs1, rs2),
            AMOXORD { rd, rs1, rs2 } => write!(f, "amoxor.d {},{},({})", rd, rs1, rs2),
            AMOANDD { rd, rs1, rs2 } => write!(f, "amoand.d {},{},({})", rd, rs1, rs2),
            AMOORD { rd, rs1, rs2 } => write!(f, "amoor.d {},{},({})", rd, rs1, rs2),
            AMOMIND { rd, rs1, rs2 } => write!(f, "amomin.d {},{},({})", rd, rs1, rs2),
            AMOMAXD { rd, rs1, rs2 } => write!(f, "amomax.d {},{},({})", rd, rs1, rs2),
            AMOMINUD { rd, rs1, rs2 } => write!(f, "amominu.d {},{},({})", rd, rs1, rs2),
            AMOMAXUD { rd, rs1, rs2 } => write!(f, "amomaxu.d {},{},({})", rd, rs1, rs2),
        }
    }
}

/// There are 6 instruction encodings (see spec 2.3)
#[derive(Debug)]
struct RType {
    rd: Reg,
    rs1: Reg,
    rs2: Reg,

    func7: u32,
    func3: u32,
}

impl From<u32> for RType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);
        let rs1 = reg_at(inst, 15);
        let rs2 = reg_at(inst, 20);
        let func7 = (inst >> 25) & 0b1111111;
        let func3 = (inst >> 12) & 0b111;

        RType {
            rd,
            rs1,
            rs2,
            func7,
            func3,
        }
    }
}

#[derive(Debug)]
struct IType {
    rd: Reg,
    rs: Reg,
    imm: i32,

    func: u32,
}

impl From<u32> for IType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);
        let rs = reg_at(inst, 15);
        let imm = (inst as i32) >> 20;
        let func = ((inst >> 12) & 0b111) as u32;

        IType { rd, rs, imm, func }
    }
}

#[derive(Debug)]
struct SType {
    rs1: Reg,
    rs2: Reg,
    imm: i32,

    func: u32,
}

impl From<u32> for SType {
    fn from(inst: u32) -> Self {
        let rs1 = reg_at(inst, 15);
        let rs2 = reg_at(inst, 20);
        let func = (inst >> 12) & 0b111;
        let imm_11_5 = (inst >> 25) & 0b1111111;
        let imm_4_0 = (inst >> 7) & 0b11111;
        let imm = (imm_11_5 << 5) | imm_4_0;
        let imm = (imm as i32) << 20 >> 20;

        SType {
            rs1,
            rs2,
            imm,
            func,
        }
    }
}

#[derive(Debug)]
struct BType {
    rs1: Reg,
    rs2: Reg,
    imm: i32,

    func: u32,
}

impl From<u32> for BType {
    fn from(inst: u32) -> Self {
        let rs1 = reg_at(inst, 15);
        let rs2 = reg_at(inst, 20);

        let func = (inst >> 12) & 0b111;
        let imm_12 = (inst >> 31) & 0b1;
        let imm_10_5 = (inst >> 25) & 0b111111;
        let imm_4_1 = (inst >> 8) & 0b1111;
        let imm_11 = (inst >> 7) & 0b1;
        let imm = (imm_12 << 12) | (imm_11 << 11) | (imm_10_5 << 5) | (imm_4_1 << 1);
        let imm = sign_extend(imm as i32, 12);

        BType {
            rs1,
            rs2,
            imm,
            func,
        }
    }
}

#[derive(Debug)]
struct UType {
    rd: Reg,
    imm: i32,
}

impl From<u32> for UType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);

        // We could shift << 12 since the two instructions that
        // use this format (LUI and AUIPC) want that, but then
        // the disassembly will not match objdump.
        let imm = (inst as i32) >> 12;

        UType { rd, imm }
    }
}

#[derive(Debug)]
struct JType {
    rd: Reg,
    imm: i32,
}

impl From<u32> for JType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);
        let imm_20 = (inst >> 31) & 0b1;
        let imm_10_1 = (inst >> 21) & 0b1111111111;
        let imm_11 = (inst >> 20) & 0b1;
        let imm_19_12 = (inst >> 12) & 0b11111111;

        let imm = (imm_20 << 20) | (imm_19_12 << 12) | (imm_11 << 11) | (imm_10_1 << 1);
        let imm = ((imm as i32) << 11) >> 11;

        JType { rd, imm }
    }
}

fn decode_32bit_instr(bits: u32) -> Option<Inst> {
    use Inst::*;

    // Opcode is in the first 7 bits of the instruction
    let opcode = bits & 0b1111111;

    let inst = match opcode {
        0b0110111 => {
            let inst = UType::from(bits);
            LUI {
                rd: inst.rd,
                imm: inst.imm,
            }
        }
        0b0010111 => {
            let inst = UType::from(bits);
            AUIPC {
                rd: inst.rd,
                imm: inst.imm,
            }
        }
        0b1101111 => {
            let inst = JType::from(bits);
            JAL {
                rd: inst.rd,
                imm: inst.imm,
            }
        }
        0b1100111 => {
            let inst = IType::from(bits);
            match inst.func {
                0b000 => JALR {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b1100011 => {
            // Conditional branches
            let inst = BType::from(bits);

            match inst.func {
                0b000 => BEQ {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b001 => BNE {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b100 => BLT {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b101 => BGE {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b110 => BLTU {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b111 => BGEU {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0000011 => {
            // Loads
            let inst = IType::from(bits);
            match inst.func {
                0b000 => LB {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b001 => LH {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b010 => LW {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b011 => LD {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b100 => LBU {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b101 => LHU {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b110 => LWU {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0100011 => {
            // Stores
            let inst = SType::from(bits);
            match inst.func {
                0b000 => SB {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b001 => SH {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b010 => SW {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b011 => SD {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0010011 => {
            // Immediate arithmetic
            let inst = IType::from(bits);
            match inst.func {
                0b000 => ADDI {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b010 => SLTI {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b011 => SLTIU {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b100 => XORI {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b110 => ORI {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b111 => ANDI {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b001 => {
                    let mode = (inst.imm >> 6) & 0b111111;
                    let shamt = inst.imm & 0b111111;
                    match mode {
                        0b000000 => SLLI {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                0b101 => {
                    let mode = (inst.imm >> 6) & 0b111111;
                    let shamt = inst.imm & 0b111111;
                    match mode {
                        0b000000 => SRLI {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt: shamt as u32,
                        },
                        0b010000 => SRAI {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt: shamt as u32,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                _ => {
                    return None;
                }
            }
        }
        0b0110011 => {
            // Register arithmetic
            let inst = RType::from(bits);
            match (inst.func7, inst.func3) {
                (0b0000000, 0b000) => ADD {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b000) => SUB {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b001) => SLL {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b010) => SLT {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b011) => SLTU {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b100) => XOR {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b101) => SRL {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b101) => SRA {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b110) => OR {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b111) => AND {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b000) => MUL {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b001) => MULH {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b010) => MULHSU {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b011) => MULHU {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b100) => DIV {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b101) => DIVU {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b110) => REM {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b111) => REMU {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0011011 => {
            let inst = IType::from(bits);
            match inst.func {
                0b000 => ADDIW {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b001 => {
                    let mode = (inst.imm >> 5) & 0b1111111;
                    let shamt = (inst.imm & 0b11111) as u32;
                    match mode {
                        0b0000000 => SLLIW {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                0b101 => {
                    let mode = (inst.imm >> 5) & 0b1111111;
                    let shamt = (inst.imm & 0b11111) as u32;
                    match mode {
                        0b0000000 => SRLIW {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        0b0100000 => SRAIW {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                _ => {
                    return None;
                }
            }
        }
        0b0111011 => {
            let inst = RType::from(bits);
            match (inst.func7, inst.func3) {
                (0b0000000, 0b000) => ADDW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b000) => SUBW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b001) => SLLW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b101) => SRLW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b101) => SRAW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b000) => MULW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b100) => DIVW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b101) => DIVUW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b110) => REMW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b111) => REMUW {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0001111 => FENCE {},
        0b1110011 => {
            if (bits >> 7) == 0 {
                ECALL
            } else if (bits >> 20) == 1 {
                EBREAK
            } else {
                return None;
            }
        }
        0b0101111 => {
            let inst = RType::from(bits);
            match inst.func3 {
                0b010 => match inst.func7 >> 2 {
                    0b00010 => LRW {
                        rd: inst.rd,
                        rs: inst.rs1,
                    },
                    0b00011 => SCW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00001 => AMOSWAPW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00000 => AMOADDW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00100 => AMOXORW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01100 => AMOANDW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01000 => AMOORW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10000 => AMOMINW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10100 => AMOMAXW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11000 => AMOMINUW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11100 => AMOMAXUW {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    _ => {
                        return None;
                    }
                },
                0b011 => match inst.func7 >> 2 {
                    0b00010 => LRD {
                        rd: inst.rd,
                        rs: inst.rs1,
                    },
                    0b00011 => SCD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00001 => AMOSWAPD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00000 => AMOADDD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00100 => AMOXORD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01100 => AMOANDD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01000 => AMOORD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10000 => AMOMIND {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10100 => AMOMAXD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11000 => AMOMINUD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11100 => AMOMAXUD {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    _ => {
                        return None;
                    }
                },
                _ => {
                    return None;
                }
            }
        }
        _ => {
            return None;
        }
    };

    Some(inst)
}

fn decode_16bit_instr(bits: u16) -> Option<Inst> {
    use Inst::*;
    use Reg::*;

    if bits == 0 {
        return None;
    }

    let inst = match bits & 0b11 {
        0b00 => {
            match bits >> 13 {
                0b000 => {
                    // ADDI4SPN
                    let rd = creg_at(bits, 2);
                    let imm_3 = (bits >> 5) & 0b1;
                    let imm_2 = (bits >> 6) & 0b1;
                    let imm_9_6 = (bits >> 7) & 0b1111;
                    let imm_5_4 = (bits >> 11) & 0b11;
                    let imm = (imm_9_6 << 6) | (imm_5_4 << 4) | (imm_3 << 3) | (imm_2 << 2);
                    let imm = sign_extend(imm as i32, 9);
                    ADDI { rd, rs: Sp, imm }
                }
                0b010 => {
                    // LW
                    let rd = creg_at(bits, 2);
                    let rs = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_2 = (bits >> 6) & 0b1;
                    let imm_6 = (bits >> 5) & 0b1;
                    let imm = (imm_6 << 6) | (imm_5_3 << 3) | (imm_2 << 2);
                    let imm = imm as i32;
                    LW { rd, rs, imm }
                }
                0b011 => {
                    // LD
                    let rd = creg_at(bits, 2);
                    let rs = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm = (imm_7_6 << 6) | (imm_5_3 << 3);
                    let imm = imm as i32;
                    LD { rd, rs, imm }
                }
                0b110 => {
                    // SW
                    let rs2 = creg_at(bits, 2);
                    let rs1 = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_2 = (bits >> 6) & 0b1;
                    let imm_6 = (bits >> 5) & 0b1;
                    let imm = (imm_6 << 6) | (imm_5_3 << 3) | (imm_2 << 2);
                    let imm = imm as i32;
                    SW { rs1, rs2, imm }
                }
                0b111 => {
                    // SD
                    let rs2 = creg_at(bits, 2);
                    let rs1 = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm = (imm_7_6 << 6) | (imm_5_3 << 3);
                    let imm = imm as i32;
                    SD { rs1, rs2, imm }
                }
                _ => {
                    return None;
                }
            }
        }
        0b01 => {
            match bits >> 13 {
                0b000 => {
                    // ADDI
                    let rd = reg_at(bits as u32, 7);
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let imm = sign_extend(imm as i32, 5);
                    ADDI { rd, rs: rd, imm }
                }
                0b001 => {
                    // ADDIW
                    let rd = reg_at(bits as u32, 7);
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let imm = sign_extend(imm as i32, 5);
                    ADDIW { rd, rs: rd, imm }
                }
                0b010 => {
                    // LI
                    let rd = reg_at(bits as u32, 7);
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let imm = sign_extend(imm as i32, 5);
                    ADDI { rd, rs: Zero, imm }
                }
                0b011 => {
                    if ((bits >> 7) & 0b11111) == 2 {
                        // ADDI16SP
                        let imm_9 = (bits >> 12) & 0b1;
                        let imm_5 = (bits >> 2) & 0b1;
                        let imm_8_7 = (bits >> 3) & 0b11;
                        let imm_6 = (bits >> 5) & 0b1;
                        let imm_4 = (bits >> 6) & 0b1;
                        let imm = (imm_9 << 9)
                            | (imm_8_7 << 7)
                            | (imm_6 << 6)
                            | (imm_5 << 5)
                            | (imm_4 << 4);
                        let imm = sign_extend(imm as i32, 9);
                        ADDI {
                            rd: Sp,
                            rs: Sp,
                            imm,
                        }
                    } else {
                        // LUI
                        let rd = reg_at(bits as u32, 7);
                        let imm_17 = (bits >> 12) & 0b1;
                        let imm_16_12 = (bits >> 2) & 0b11111;
                        let imm = ((imm_17 as u32) << 17) | ((imm_16_12 as u32) << 12);
                        let imm = sign_extend(imm as i32, 17);
                        LUI { rd, imm: imm >> 12 }
                    }
                }
                0b100 => {
                    match (bits >> 10) & 0b11 {
                        0b00 => {
                            // SRLI
                            let rd = creg_at(bits, 7);
                            let imm_5 = (bits >> 12) & 0b1;
                            let imm_4_0 = (bits >> 2) & 0b11111;
                            let imm = (imm_5 << 5) | imm_4_0;
                            let shamt = imm as u32;
                            SRLI { rd, rs: rd, shamt }
                        }
                        0b01 => {
                            // SRAI
                            let rd = creg_at(bits, 7);
                            let imm_5 = (bits >> 12) & 0b1;
                            let imm_4_0 = (bits >> 2) & 0b11111;
                            let imm = (imm_5 << 5) | imm_4_0;
                            let shamt = imm as u32;
                            SRAI { rd, rs: rd, shamt }
                        }
                        0b10 => {
                            // ANDI
                            let rd = creg_at(bits, 7);
                            let imm_5 = (bits >> 12) & 0b1;
                            let imm_4_0 = (bits >> 2) & 0b11111;
                            let imm = (imm_5 << 5) | imm_4_0;
                            let imm = sign_extend(imm as i32, 5);
                            ANDI { rd, rs: rd, imm }
                        }
                        0b11 => {
                            let rd = creg_at(bits, 7);
                            let rs2 = creg_at(bits, 2);
                            match ((bits >> 12) & 0b1, (bits >> 5) & 0b11) {
                                (0b0, 0b00) => SUB { rd, rs1: rd, rs2 },
                                (0b0, 0b01) => XOR { rd, rs1: rd, rs2 },
                                (0b0, 0b10) => OR { rd, rs1: rd, rs2 },
                                (0b0, 0b11) => AND { rd, rs1: rd, rs2 },
                                (0b1, 0b00) => SUBW { rd, rs1: rd, rs2 },
                                (0b1, 0b01) => ADDW { rd, rs1: rd, rs2 },
                                _ => return None,
                            }
                        }
                        _ => {
                            return None;
                        }
                    }
                }
                0b101 => {
                    // J
                    let imm_5 = (bits >> 2) & 0b1;
                    let imm_3_1 = (bits >> 3) & 0b111;
                    let imm_7 = (bits >> 6) & 0b1;
                    let imm_6 = (bits >> 7) & 0b1;
                    let imm_10 = (bits >> 8) & 0b1;
                    let imm_9_8 = (bits >> 9) & 0b11;
                    let imm_4 = (bits >> 11) & 0b1;
                    let imm_11 = (bits >> 12) & 0b1;
                    let imm = (imm_11 << 11)
                        | (imm_10 << 10)
                        | (imm_9_8 << 8)
                        | (imm_7 << 7)
                        | (imm_6 << 6)
                        | (imm_5 << 5)
                        | (imm_4 << 4)
                        | (imm_3_1 << 1);
                    let imm = sign_extend(imm as i32, 11);
                    JAL { rd: Zero, imm }
                }
                0b110 => {
                    // BEQZ
                    let rs1 = creg_at(bits, 7);
                    let imm_5 = (bits >> 2) & 0b1;
                    let imm_2_1 = (bits >> 3) & 0b11;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm_4_3 = (bits >> 10) & 0b11;
                    let imm_8 = (bits >> 12) & 0b1;
                    let imm = (imm_8 << 8)
                        | (imm_7_6 << 6)
                        | (imm_5 << 5)
                        | (imm_4_3 << 3)
                        | (imm_2_1 << 1);
                    let imm = sign_extend(imm as i32, 8);
                    BEQ {
                        rs1,
                        rs2: Zero,
                        imm,
                    }
                }
                0b111 => {
                    // BNEZ
                    let rs1 = creg_at(bits, 7);
                    let imm_5 = (bits >> 2) & 0b1;
                    let imm_2_1 = (bits >> 3) & 0b11;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm_4_3 = (bits >> 10) & 0b11;
                    let imm_8 = (bits >> 12) & 0b1;
                    let imm = (imm_8 << 8)
                        | (imm_7_6 << 6)
                        | (imm_5 << 5)
                        | (imm_4_3 << 3)
                        | (imm_2_1 << 1);
                    let imm = sign_extend(imm as i32, 8);
                    BNE {
                        rs1,
                        rs2: Zero,
                        imm,
                    }
                }
                _ => {
                    return None;
                }
            }
        }
        0b10 => {
            match (bits >> 13) & 0b111 {
                0b000 => {
                    // SLLI
                    let rd = reg_at(bits as u32, 7);
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let shamt = imm as i32;
                    SLLI { rd, rs: rd, shamt }
                }
                0b010 => {
                    // LWSP
                    let rd = reg_at(bits as u32, 7);
                    let imm_7_6 = (bits >> 2) & 0b11;
                    let imm_4_2 = (bits >> 4) & 0b111;
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm = (imm_7_6 << 6) | (imm_5 << 5) | (imm_4_2 << 2);
                    let imm = imm as i32;
                    LW { rd, rs: Sp, imm }
                }
                0b011 => {
                    // LDSP
                    let rd = reg_at(bits as u32, 7);
                    let imm_8_6 = (bits >> 2) & 0b111;
                    let imm_4_3 = (bits >> 5) & 0b11;
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm = (imm_8_6 << 6) | (imm_5 << 5) | (imm_4_3 << 3);
                    let imm = imm as i32;
                    LD { rd, rs: Sp, imm }
                }
                0b100 => {
                    let imm12 = (bits >> 12) & 0b1;
                    let rs1 = reg_at(bits as u32, 7);
                    let rs2 = reg_at(bits as u32, 2);
                    match (imm12, rs1, rs2) {
                        (0, rs, Reg::Zero) => {
                            JALR {rd: Zero, rs, imm: 0}
                        }
                        (0, rd, rs2) => {
                            ADD {rd, rs1: Zero, rs2}
                        }
                        (1, Zero, Zero) => {
                            EBREAK
                        }
                        (1, rs, Zero) => {
                            JALR {rd: Ra, rs, imm: 0}
                        }
                        (1, rd, rs2) => {
                            ADD {rd, rs1: rd, rs2}
                        }
                        _ => {
                            return None;
                        }
                   }
                }
                0b110 => {
                    // SWSP
                    let rs2 = reg_at(bits as u32, 2);
                    let imm_7_6 = (bits >> 7) & 0b11;
                    let imm_5_2 = (bits >> 9) & 0b1111;
                    let imm = (imm_7_6 << 6) | (imm_5_2 << 2);
                    let imm = imm as i32;
                    SW { rs1: Sp, rs2, imm }
                }
                0b111 => {
                    // SDSP
                    let rs2 = reg_at(bits as u32, 2);
                    let imm_8_6 = (bits >> 7) & 0b111;
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm = (imm_8_6 << 6) | (imm_5_3 << 3);
                    let imm = imm as i32;
                    SD { rs1: Sp, rs2, imm }
                }
                _ => {
                    return None;
                }
            }
        }
        _ => {
            return None;
        }
    };

    Some(inst)
}

/// Decodes an instruction.  Also returns the width of the decoded
/// instruction for incrementing the PC.  This allows us to handle
/// the compressed instructions too.
pub fn decode_instr(bits: u32) -> Option<(Inst, u64)> {
    if (bits & 3) == 3 {
        let inst = decode_32bit_instr(bits)?;
        Some((inst, 4))
    } else {
        let inst = decode_16bit_instr(bits as u16)?;
        Some((inst, 2))
    }
}
