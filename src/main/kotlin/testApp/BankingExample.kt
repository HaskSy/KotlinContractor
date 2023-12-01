package testApp

import contractor.annotations.Contracted
import contractor.annotations.Ensures
import contractor.annotations.Requires

@Contracted
class BankingExample {

    companion object {
        const val MAX_BALANCE: Int = 1000
    }

    /*@ spec_public @*/ private var balance: Int = 0
    /*@ spec_public @*/ private var isLocked: Boolean = false

    //@ public invariant balance >= 0 && balance <= MAX_BALANCE;

    //@ assignable balance;
    @Ensures()
    constructor() {
        @Ensures contractorCondition (balance == 0)
        this.balance = 0
    }

    //@ assignable balance;
    fun credit(amount: Int) {
        @Requires contractorCondition(0 < amount && amount + balance < MAX_BALANCE)
        @Ensures contractorCondition(balance == old(balance) + amount)
        this.balance += amount
    }

    //@ assignable balance;
    fun debit(amount: Int) {
        @Requires contractorCondition(0 < amount && amount <= balance)
        @Ensures contractorCondition (balance == old(balance) - amount)
        this.balance -= amount
    }

    fun lockAccount() {
        @Ensures contractorCondition(isLocked)
        this.isLocked = true
    }

    //@   requires !isLocked;
    //@   ensures \result == balance;
    //@ also
    //@   requires isLocked;
    //@   signals_only BankingException;
    /*@ pure @*/
    @Throws(Exception::class)
    fun getBalance(): Int {
        return if (!this.isLocked) {
            this.balance
        } else {
            throw Exception()
        }
    }
}

fun contractorCondition(value: Boolean) {
}

fun <T> old(value: T): T {
    return value
}
