pub const MEM_SIZE: MemAddress = 0xFFFF;

pub type MemAddress = u16;

pub struct VM {
    memory: [u8; MEM_SIZE as usize],
    pc: MemAddress,

    register_accumulator: u8,
    register_x: u8,
    register_y: u8,

    flags: Flags,
}

#[derive(Default)]
#[allow(unused)]
pub struct Flags {
    carry: bool,
    zero: bool,
    interrupt_disable: bool,
    decimal_mode: bool,
    break_command: bool,
    overflow: bool,
    negative: bool,
}

#[derive(thiserror::Error, Debug)]
pub enum ProgramError {
    #[error("Out of memory")]
    OOM,
    #[error("Program had reached the end")]
    EOF,
    #[error("Bad instruction: {0:#02x}")]
    BadInstruction(u8),
    #[error("{0}")]
    ArgumentError(String),
}

type ProgramResult<V = ()> = Result<V, ProgramError>;

#[allow(unused)]
enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Relative,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Indirect,
    IndirectX,
    IndirectY,
}

impl VM {
    pub fn new() -> Self {
        Self {
            memory: [0; MEM_SIZE as usize],
            pc: 0,
            register_accumulator: 0,
            register_x: 0,
            register_y: 0,
            flags: Default::default(),
        }
    }

    pub fn load_program(&mut self, code: &[u8]) {
        self.memory[0x8000..(0x8000 + code.len())].copy_from_slice(&code[..]);
        self.pc = 0x8000;
    }

    pub fn run(&mut self) -> ProgramResult {
        loop {
            match self.next_instruction()? {
                0xA9 => self.lda(AddressingMode::Immediate)?,
                0xA5 => self.lda(AddressingMode::ZeroPage)?,
                0xB5 => self.lda(AddressingMode::ZeroPageX)?,
                0xAD => self.lda(AddressingMode::Absolute)?,
                0xBD => self.lda(AddressingMode::AbsoluteX)?,
                0xB9 => self.lda(AddressingMode::AbsoluteY)?,
                0xA1 => self.lda(AddressingMode::IndirectX)?,
                0xB1 => self.lda(AddressingMode::IndirectY)?,
                0xAA => self.tax()?,
                0xE8 => self.inx()?,
                0x4C => self.jmp(AddressingMode::Absolute)?,
                0x6C => self.jmp(AddressingMode::Indirect)?,
                00 => {
                    break;
                }
                bad_instruction => return Err(ProgramError::BadInstruction(bad_instruction)),
            };
        }
        Ok(())
    }

    fn next_instruction(&mut self) -> Result<u8, ProgramError> {
        let result = self.memory[self.pc as usize];
        self.pc += 1;
        Ok(result)
    }

    fn next_u16(&mut self) -> ProgramResult<u16> {
        let low = self.next_instruction()? as u16;
        let high = self.next_instruction()? as u16;
        Ok(high << 8 | low)
    }

    fn jmp(&mut self, addressing_mode: AddressingMode) -> ProgramResult {
        let addr = self.get_operand_address(addressing_mode)?;
        self.pc = addr;
        Ok(())
    }

    fn lda(&mut self, addressing_mode: AddressingMode) -> ProgramResult {
        let addr = self.get_operand_address(addressing_mode)?;
        self.register_accumulator = self.read_memory(addr)?;
        self.set_status(self.register_accumulator);
        Ok(())
    }

    fn get_operand_address(&mut self, mode: AddressingMode) -> ProgramResult<MemAddress> {
        match mode {
            AddressingMode::Immediate => {
                let addr = self.pc;
                self.pc += 1;
                Ok(addr)
            }
            AddressingMode::ZeroPage => {
                Ok(self.next_instruction()? as MemAddress)
            }
            AddressingMode::ZeroPageX => {
                let (addr, _) = self.next_instruction()?.overflowing_add(self.register_x);
                Ok(addr as MemAddress)
            }
            AddressingMode::ZeroPageY => {
                let (addr, _) = self.next_instruction()?.overflowing_add(self.register_y);
                Ok(addr as MemAddress)
            }
            AddressingMode::Relative => {
                let offset = self.next_instruction()?;
                let addr = if offset & 0b1000_0000 == 0x00 {
                    self.pc + (offset as MemAddress)
                } else {
                    self.pc - (offset & 0b0111_1111) as MemAddress
                };
                Ok(addr)
            }
            AddressingMode::Absolute => {
                self.next_u16()
            }
            AddressingMode::AbsoluteX => {
                let (addr, _) = self.next_u16()?.overflowing_add(self.register_x as MemAddress);
                Ok(addr)
            }
            AddressingMode::AbsoluteY => {
                let (addr, _) = self.next_u16()?.overflowing_add(self.register_x as MemAddress);
                Ok(addr)
            }
            AddressingMode::Indirect => {
                let addr = self.next_u16()?;
                let low = self.read_memory(addr)? as u16;
                let high = self.read_memory(addr + 1)? as u16;
                Ok(high << 8 | low)
            }
            AddressingMode::IndirectX => {
                let (addr, _) = self.next_instruction()?.overflowing_add(self.register_x);
                let low = self.read_memory(addr as u16)? as u16;
                let high = self.read_memory(addr as u16 + 1)? as u16;
                Ok(high << 8 | low)
            }
            AddressingMode::IndirectY => {
                let (addr, _) = self.next_instruction()?.overflowing_add(self.register_y);
                let low = self.read_memory(addr as u16)? as u16;
                let high = self.read_memory(addr as u16 + 1)? as u16;
                Ok(high << 8 | low)
            }
        }
    }

    fn tax(&mut self) -> ProgramResult {
        self.register_x = self.register_accumulator;
        self.set_status(self.register_x);
        Ok(())
    }

    fn inx(&mut self) -> ProgramResult {
        let (result, overflow) = (self.register_x as i8).overflowing_add(1);
        self.register_x = result as u8;
        self.flags.overflow = overflow;
        self.set_status(self.register_x);
        Ok(())
    }

    fn set_status(&mut self, last_value: u8) {
        self.flags.zero = last_value == 0;
        self.flags.negative = last_value & 0b1000_0000 != 0;
    }

    fn read_memory(&self, addr: u16) -> ProgramResult<u8> {
        Ok(self.memory[addr as usize])
    }
}

#[cfg(test)]
mod tests {
    use crate::VM;

    #[test]
    fn test_type_cast() {
        let a: u8 = 0xff;
        let b = a as i8;
        assert_eq!(b, -1);

        let (result, overflowed) = 0x7Fi8.overflowing_add(1);
        assert_eq!(result, -128);
        assert!(overflowed);
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut vm = VM::new();
        vm.load_program(&[0xa9, 0xc0, 0xaa, 0xe8, 0x00]);
        vm.run().unwrap();
        assert_eq!(vm.register_x, 0xc1);
    }

    #[test]
    fn test_inx_overflow() {
        let mut vm = VM::new();
        vm.register_x = 0xff;
        vm.load_program(&[0xe8, 0xe8, 0x00]);
        vm.run().unwrap();
        assert_eq!(vm.register_x, 1)
    }
}
