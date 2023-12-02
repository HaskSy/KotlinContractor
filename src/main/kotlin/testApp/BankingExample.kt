package testApp

import contractor.annotations.ClassInvariant
import contractor.annotations.Ensures
import contractor.annotations.Requires
import kotlin.reflect.full.memberProperties
import kotlin.reflect.jvm.isAccessible

class BankingExample {

    companion object {
        const val MAX_BALANCE: Int = 1000
    }

    private var balance: Int = 0
    private var isLocked: Boolean = false
    private var selfReference = this

    constructor() {
        this.balance = 0
    }

    fun credit(amount: Int) = dbc {
        requires { 0 < amount && amount + balance < MAX_BALANCE }
        ensures { old<Int>(selfReference, "balance") + amount == balance }
        balance += amount
    }


    //@ assignable balance;
    fun debit(amount: Int) {
//        @Requires contractorCondition(0 < amount && amount <= balance)
//        @Ensures contractorCondition(balance == old(balance) - amount)
        this.balance -= amount
    }

    fun lockAccount() {
//        @Ensures contractorCondition (isLocked)
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

fun main() {
    val test = BankingExample()
    test.credit(100)
    test.credit(100)
}
