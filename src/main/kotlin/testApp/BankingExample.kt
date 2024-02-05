package testApp

class BankingExample {

    companion object {
        const val MAX_BALANCE: Int = 1000
    }

    private var balance: Int = 0

    constructor() {
        this.balance = 0
    }

    fun credit(amount: Int) = dbc(this) {
        requires { 0 < amount && amount + balance < MAX_BALANCE }
        ensures { old(BankingExample::balance) + amount == balance }
        balance += amount
    }


    fun debit(amount: Int) = dbc(this) {
        requires { 0 < amount && amount + balance <= MAX_BALANCE }
        ensures { old(BankingExample::balance) - amount == balance }
        balance -= amount
    }
}

fun main() {
    val test = BankingExample()
    test.credit(100)
    test.credit(100)
}
