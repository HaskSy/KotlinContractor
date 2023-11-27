package org.example.contractor

@ClassInvariant("balance >= 0 && balance <= MAX_BALANCE")
//@Ensures("balance == 0")
class BankingExample {
    private var balance = 0
    private var isLocked = false

    @Requires("requires 0 < amount && amount + balance < MAX_BALANCE")
    @Ensures("balance == @Old(balance) + amount")
    fun credit(amount: Int) {
        balance += amount
    }

    @Requires("0 < amount && amount <= balance")
    @Ensures("balance == @Old(balance) - amount")
    fun debit(amount: Int) {
        balance -= amount
    }

    @Ensures("isLocked == true")
    fun lockAccount() {
        isLocked = true
    }

    //@   requires !isLocked;
    //@   ensures \result == balance;
    //@ also
    //@   requires isLocked;
    //@   signals_only BankingException;
    /*@ pure @*/ fun getBalance(): Int {
        return if (!isLocked) {
            balance
        } else {
            throw Exception();
        }
    }

    companion object {
        const val MAX_BALANCE = 1000
    }
}
