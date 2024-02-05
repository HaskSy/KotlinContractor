package testApp

import kotlin.reflect.KMutableProperty1
import kotlin.reflect.KProperty1
import kotlin.reflect.jvm.isAccessible

@DslMarker
annotation class DbCM;

fun <T> dbc(thisRef: Any, block: ContractContext.() -> T): T {
    var isVerifying: Boolean
    lateinit var ctx: ContractContext
    val requiresList: MutableList<() -> Boolean> = mutableListOf();
    val ensuresList: MutableList<() -> Boolean> = mutableListOf();

    try {

        isVerifying = false
        ctx = object : ContractContext {
            private val oldValues = mutableMapOf<String, Any?>()
            override fun requires(precondition: () -> Boolean) {
                requiresList.add(precondition)
                if (!precondition()) {
                    System.err.println("Precondition is not satisfied, unexpected behaviour might occur")
                }
            }

            override fun ensures(postcondition: () -> Boolean) {
                ensuresList.add(postcondition)
                postcondition() // If there's function 'old' - calls it
            }

            override fun <T> old(property: KMutableProperty1<out Any, T>): T {
                if (!isVerifying) {
                    val casted = property as KProperty1<Any, T>
                    storeOldValue(thisRef, casted)
                }
                return oldValues[property.name] as? T
                    ?: throw IllegalArgumentException("No old value stored for ${property.name} or type mismatch")
            }

//            private fun storeOldValue(receiver: Any, propertyName: String) {
//                val property = receiver::class.memberProperties.first { it.name == propertyName } as KProperty1<Any, *>
//                val oldAccessibility = property.isAccessible
//                property.isAccessible = true
//                oldValues[property.name] = property.get(receiver)
//                property.isAccessible = oldAccessibility
//            }

            private fun <T> storeOldValue(receiver: Any, property: KProperty1<Any, T>) {
                val oldAccessibility = property.isAccessible
                property.isAccessible = true
                oldValues[property.name] = property.get(receiver)
                property.isAccessible = oldAccessibility
            }
        }
        return ctx.block()
    } finally {
        isVerifying = true

        for (requiresLambda in requiresList) {
            if (!requiresLambda()) throw IllegalArgumentException("Precondition not satisfied")
        }

        for (ensuresLambda in ensuresList) {
            if (!ensuresLambda()) throw IllegalArgumentException("Postcondition not satisfied")
        }

    }
}

interface ContractContext {
    fun requires(precondition: () -> Boolean)
    fun ensures(postcondition: () -> Boolean)
    fun <T> old(property: KMutableProperty1<out Any, T>): T
}

//interface Contracted {
//    fun requires(precondition: () -> Boolean)
//    fun ensures(postcondition: () -> Boolean)
//    fun <T, V> old(obj: T, name: String): V
//}
//
//class ContractedInvocationHandler<T>(private val instance: T): InvocationHandler {
//
//    private val oldValues = mutableMapOf<String, Any>()
//    override fun invoke(proxy: Any?, method: Method?, args: Array<out Any>?): Any? {
//        val nonNullArgs = args ?: arrayOf()
//        println(args.contentToString())
//        return method?.invoke(instance, *nonNullArgs)
//    }
//}
