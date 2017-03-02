# encoding: UTF-8

"""
海龟交易

注意事项：
1. 作者不对交易盈利做任何保证，策略代码仅供参考
2. 本策略需要用到talib，没有安装的用户请先参考www.vnpy.org上的教程安装
3. 将IF0000_1min.csv用ctaHistoryData.py导入MongoDB后，直接运行本文件即可回测策略

"""


from ctaBase import *
from multiCtaTemplate import MultiCtaTemplate
import shelve
import talib
import numpy as np
from collections import OrderedDict
import time
from datetime import datetime

from eventEngine import *
from vtConstant import *
from vtGateway import VtSubscribeReq, VtOrderReq, VtCancelOrderReq, VtLogData

# turtle state
TURTLE_READY = "turtleReady"
TURTLE_OPEN_ONE = "turtleOne"
TURTLE_OPEN_TWO = "turtleTwo"
TURTLE_OPEN_THREE = "turtleThree"
TURTLE_OPEN_FOUR = "turtleFour"
TURTLE_STOP = "turtleStop"

########################################################################
class TurtleStrategy(MultiCtaTemplate):
    """turtle"""
    className = 'TurtleStrategy'
    author = u'Young'
    
    turtleFileName = "turtlePosition.vt"
    
    # 策略参数
    atrLength = 20          # 计算ATR指标的窗口数   
    atrMaLength = 10        # 计算ATR均线的窗口数
    rsiLength = 5           # 计算RSI的窗口数
    rsiEntry = 16           # RSI的开仓信号
    trailingPercent = 0.8   # 百分比移动止损
    initDays = 3           # 初始化数据所用的天数
    maxDrawback = 0.01     #最大回撤

    # 策略变量
    bufferSize = 30                    # 需要缓存的数据的大小


    rsiValue = 0                        # RSI指标的数值
    rsiBuy = 0                          # RSI买开阈值
    rsiSell = 0                         # RSI卖开阈值
    intraTradeHigh = 0                  # 移动止损用的持仓期内最高价
    intraTradeLow = 0                   # 移动止损用的持仓期内最低价

    minStrategy = True    
    dayStrategy = False

    # 参数列表，保存了参数的名称
    paramList = ['name',
                 'className',
                 'vtSymbolList',
                 'tenDayHigh',
                 'tenDayLow',
                 'twentyDayHigh',
                 'twentyDayLow',
                 'openVolume',
                 'buyPriceList',
                 'shortPriceList',
                 'stopPriceList',
                 'atrValue',
                 'lastPriceList'
                 ]    

    # 变量列表，保存了变量的名称
    varList = ['inited',
               'trading',
               'pos',
               'atrValue']  

    #----------------------------------------------------------------------
    def __init__(self, ctaEngine, setting):
        """Constructor"""
        super(TurtleStrategy, self).__init__(ctaEngine, setting)
        
        # 注意策略类中的可变对象属性（通常是list和dict等），在策略初始化时需要重新创建，
        # 否则会出现多个策略实例之间数据共享的情况，有可能导致潜在的策略逻辑错误风险，
        # 策略类中的这些可变对象属性可以选择不写，全都放在__init__下面，写主要是为了阅读
        # 策略时方便（更多是个编程习惯的选择）  
        
        #全局只有一个的变量
 
        #已经发单的合约记录。
        #任何合约如果有已经发出的单子，就不允许重新再发新的单子。
        #合约成交或者撤单后，将该合约从字典中删除。        
        self.workingBuyList = {}
        self.workingShortList = {}
        self.workingStopList = {}

        self.orderList = {}                      # 保存委托代码的列表

        self.bufferCount = {}
        self.bar = {}
        self.barMinute = {}
        self.barDay = {}        

        self.highArray = {}
        self.lowArray = {}
        self.closeArray = {}
        
        self.atrCount = {}
        self.atrArray = {}
        self.atrValue = {}
        self.turtlePositionList = {}
        
        self.tenDayHigh = {}
        self.tenDayLow = {}
        self.twentyDayHigh = {}
        self.twentyDayLow = {}

        self.openVolume = {}

        #主要的价格列表，记录了当前各个合约的预计开仓价格
        #多单buy，空单short
        self.buyPriceList = {}
        self.shortPriceList = {}

        #主要的止损单价格列表        
        self.stopPriceList = {}
        
        #current price
        self.lastPriceList = {}
        
        self.debugInit = True

        self.balance = 0
        self.available = 0        
        self.highestBalance = 0
        
        for s in self.vtSymbolList:
            self.bufferCount[s] = 0                     # 目前已经缓存了的数据的计数
            self.bar[s] = None                  # K线对象
            self.barMinute[s] = EMPTY_STRING    # K线当前的分钟
            self.barDay[s] = EMPTY_STRING    # K线当前的分钟
            
            self.highArray[s] = np.zeros(self.bufferSize)    # K线最高价的数组
            self.lowArray[s] = np.zeros(self.bufferSize)     # K线最低价的数组
            self.closeArray[s] = np.zeros(self.bufferSize)   # K线收盘价的数组
            
            self.atrCount[s] = 0                        # 目前已经缓存了的ATR的计数
            self.atrArray[s] = np.zeros(self.bufferSize)     # ATR指标的数组
            self.atrValue[s] = EMPTY_FLOAT                   # 最新的ATR指标数值
            self.turtlePositionList[s] = None
            
            self.tenDayHigh[s] = EMPTY_FLOAT  #10日最高
            self.tenDayLow[s] = EMPTY_FLOAT  #10日最低
            self.twentyDayHigh[s] = EMPTY_FLOAT  #20日最高            
            self.twentyDayLow[s] = EMPTY_FLOAT  #20日最低

            self.openVolume[s] = EMPTY_INT      #开仓手数

            self.buyPriceList[s] = EMPTY_FLOAT
            self.shortPriceList[s] = EMPTY_FLOAT
    
            #主要的止损单价格列表        
            self.stopPriceList[s] = EMPTY_FLOAT
            
            self.lastPriceList[s] = EMPTY_FLOAT
            
            self.orderList[s] = EMPTY_STRING
                        
    #----------------------------------------------------------------------
    def onInit(self):
        """初始化策略（必须由用户继承实现）"""
        self.writeCtaLog(u'%s策略初始化' %self.name)
        
        self.debugInit = False
        # 载入历史数据，并采用回放计算的方式初始化策略数值
        for s in self.vtSymbolList:
            initData = self.loadBar(s, self.initDays)
            for bar in initData:
                self.onBar(bar)

        self.debugInit = True
        self.putEvent()

    #----------------------------------------------------------------------
    def onStart(self):
        """启动策略（必须由用户继承实现）"""
        self.writeCtaLog(u'%s策略启动' %self.name)
        self.putEvent()

    #----------------------------------------------------------------------
    def onStop(self):
        """停止策略（必须由用户继承实现）"""
        self.writeCtaLog(u'%s策略停止' %self.name)
        self.putEvent()

    #----------------------------------------------------------------------
    def onTick(self, tick):
        """收到行情TICK推送（必须由用户继承实现）"""
        # 计算K线
        symbol = tick.vtSymbol
        hasWorkingOrder = self.workingBuyList.has_key(symbol) or self.workingShortList.has_key(symbol)
        if self.openVolume[symbol] > 0 and hasWorkingOrder != True:
            ## 判断是否要进行交易
            
            if self.buyPriceList[symbol] > 0:
                buyPrice = self.buyPriceList[symbol]
            else:
                ## buy price is 0 or -1
                ## do not open any position
                buyPrice = 999999999

            if self.shortPriceList[symbol] > 0:
                shortPrice = self.shortPriceList[symbol]
            else:
                #short price is 0 or -1
                #do not open any position
                shortPrice = 0

            if tick.lastPrice > buyPrice:
                #buy
                #tick价格+5个整数点，需要去根据合约单位去细化
                orderID = self.buy(symbol, tick.lastPrice+5, self.openVolume[symbol])
                self.workingBuyList[symbol] = orderID
                if self.orderList[symbol] != EMPTY_STRING:
                    self.writeCtaLog(u'%s已存在报单：合约号: %s' %(symbol, self.orderList[symbol]))
                else:
                    self.orderList[symbol] = orderID
                self.writeCtaLog(u'%s多头开仓：价格:%d, 手数：%d， 合约号: %s' %(symbol, tick.lastPrice+5, self.openVolume[symbol], orderID)) 
            elif tick.lastPrice < shortPrice:
                #short
                orderID = self.short(symbol, tick.lastPrice-5, self.openVolume[symbol])
                self.workingShortList[symbol] = orderID
                if self.orderList[symbol] != EMPTY_STRING:
                    self.writeCtaLog(u'%s已存在报单：合约号: %s' %(symbol, self.orderList[symbol]))
                else:
                    self.orderList[symbol] = orderID
                self.writeCtaLog(u'%s空头开仓：价格:%d, 手数：%d， 合约号: %s' %(symbol, tick.lastPrice+5, self.openVolume[symbol], orderID))                 
            else:
                #do not open any position
                pass
            
            end = time.clock()               
    
        elif self.workingBuyList.has_key(symbol) == True:
            #self.writeCtaLog(u'已有报单未返回：%s' %symbol)
            pass
        else:
            #总资金太少，无法开仓
            #self.writeCtaLog(u'总资金不足，无法开仓：%s' %symbol)
            pass

        self.lastPriceList[symbol] = tick.lastPrice

        end = time.clock()               

        if self.minStrategy:
            tickMinute = tick.datetime.minute            
            if tickMinute != self.barMinute[symbol]:
                if self.bar[symbol]:
                    self.onBar(self.bar[symbol])
    
                bar = CtaBarData()              
                bar.vtSymbol = tick.vtSymbol
                bar.symbol = tick.symbol
                bar.exchange = tick.exchange
    
                bar.open = tick.lastPrice
                bar.high = tick.lastPrice
                bar.low = tick.lastPrice
                bar.close = tick.lastPrice
    
                bar.date = tick.date
                bar.time = tick.time
                bar.datetime = tick.datetime    # K线的时间设为第一个Tick的时间
    
                self.bar[symbol] = bar                  # 这种写法为了减少一层访问，加快速度
                self.barMinute[symbol] = tickMinute   # 更新当前的分钟
            else:                               # 否则继续累加新的K线
                bar = self.bar[symbol]                  # 写法同样为了加快速度
    
                bar.high = max(bar.high, tick.lastPrice)
                bar.low = min(bar.low, tick.lastPrice)
                bar.close = tick.lastPrice
        elif self.dayStrategy:
            tickDay = tick.datetime.day
            # 如果第一个TICK或者新的一分钟
            if tickDay != self.barDay[symbol]:
                if self.bar[symbol]:
                    self.onBar(self.bar[symbol])

                bar = CtaBarData()              
                bar.vtSymbol = tick.vtSymbol
                bar.symbol = tick.symbol
                bar.exchange = tick.exchange
    
                bar.open = tick.lastPrice
                bar.high = tick.lastPrice
                bar.low = tick.lastPrice
                bar.close = tick.lastPrice
    
                bar.date = tick.date
                bar.time = tick.time
                bar.datetime = tick.datetime    # K线的时间设为第一个Tick的时间
                    
                bar.volume = tick.volume
                bar.openInterest = tick.openInterest
                self.bar[symbol] = bar                  # 这种写法为了减少一层访问，加快速度
                self.barDay[symbol] = tickDay           # 更新当前的分钟
            # 否则继续累加新的K线
            else: 
                bar = self.bar[symbol]                  # 写法同样为了加快速度                
                bar.high = max(bar.high, tick.lastPrice)
                bar.low = min(bar.low, tick.lastPrice)
                bar.close = tick.lastPrice
        else:
            pass

    #----------------------------------------------------------------------
    def onBar(self, bar):
        """收到Bar推送（必须由用户继承实现）"""
        # 撤销之前发出的尚未成交的委托（包括限价单和停止单）

        symbol = bar.symbol
        if self.orderList[symbol] != EMPTY_STRING:
            orderID = self.orderList[symbol]
            self.cancelOrder(orderID)
            if self.workingShortList.has_key(symbol) and self.workingShortList[symbol] == orderID:
                self.writeCtaLog(u'%s取消空单报单：%s' %(symbol, orderID))                
                del self.workingShortList[symbol]
                self.orderList[symbol] = EMPTY_STRING
            if self.workingBuyList.has_key(symbol) and self.workingBuyList[symbol] == orderID:
                self.writeCtaLog(u'%s取消多单报单：%s' %(symbol, orderID))                                
                del self.workingBuyList[symbol]
                self.orderList[symbol] = EMPTY_STRING


        # 保存K线数据
        self.closeArray[symbol][0:self.bufferSize-1] = self.closeArray[symbol][1:self.bufferSize]
        self.highArray[symbol][0:self.bufferSize-1] = self.highArray[symbol][1:self.bufferSize]
        self.lowArray[symbol][0:self.bufferSize-1] = self.lowArray[symbol][1:self.bufferSize]
        
        self.closeArray[symbol][-1] = bar.close
        self.highArray[symbol][-1] = bar.high
        self.lowArray[symbol][-1] = bar.low
        
        self.bufferCount[symbol] += 1
        if self.bufferCount[symbol] < self.bufferSize:
            return
        
        #计算二十日最高，最低，十日最高最低。
        if self.bufferCount[symbol] >= 20:
            self.tenDayHigh[symbol] = max(self.highArray[symbol][self.bufferSize-10:self.bufferSize-1])
            self.tenDayLow[symbol] = min(self.lowArray[symbol][self.bufferSize-10:self.bufferSize-1])
            self.twentyDayHigh[symbol] = max(self.highArray[symbol][self.bufferSize-20:self.bufferSize-1])
            self.twentyDayLow[symbol] = min(self.lowArray[symbol][self.bufferSize-20:self.bufferSize-1])
        

        # 计算指标数值
        self.atrValue[symbol] = talib.ATR(self.highArray[symbol], 
                                          self.lowArray[symbol], 
                                          self.closeArray[symbol],
                                          self.atrLength)[-1]
        self.atrArray[symbol][0:self.bufferSize-1] = self.atrArray[symbol][1:self.bufferSize]
        self.atrArray[symbol][-1] = self.atrValue[symbol]
    
        self.atrCount[symbol] += 1
        if self.atrCount[symbol] <= 0:
            return
    
        #计算开仓手数        
        self.openVolume[symbol] = self.calculateOpenPosition(symbol, bar.close, self.atrValue[symbol])

        #更新海龟持仓对象
        #1. 未开仓的turtle，创建turtle对象
        #2. 已开仓的对象，更新atr以及相应的openPrice（这个是否需要有待考察）
        if self.turtlePositionList[symbol] == None:
            tur = turtlePosition(self)
            tur.vtSymbol = bar.vtSymbol
            tur.symbol = bar.symbol
            #tur.exchange = bar.exchange
            tur.currentState = TURTLE_READY
            self.turtlePositionList[symbol] = tur

        self.turtlePositionList[symbol].updateAtrData(self.atrValue[symbol])

        #更新价格，止损单并发送到本地。
        self.setPriceList(symbol)
                    
        # 发出状态更新事件
        self.putEvent()

    #----------------------------------------------------------------------
    def onOrder(self, order):
        """收到委托变化推送（必须由用户继承实现）"""
        
        pass


    #----------------------------------------------------------------------
    def onAccount(self, account):
        """收到Account变化推送（必须由用户继承实现）"""
        self.balance = account.balance
        self.available = account.available

        if self.balance <= (self.highestBalance * self.maxDrawback):
            self.writeCtaLog(u'Sell All. balance:%s ##highest:%s,' %(self.balance, self.highestBalance))
            #sell all position
            self.sellAll()
        self.highestBalance = max(self.highestBalance, self.balance)
        
    #----------------------------------------------------------------------
    def sellAll(self):
        """清仓"""
        for i in self.pos:
            if pos[i] > 0:
                self.sell(i, self.lastPriceList[i]-10, pos[i], False)
                self.writeCtaLog(u'%s平多,数量：%s,价格：%s' %(i, pos[i],self.lastPriceList[i]-10))
            elif pos[i] < 0:
                self.cover(i, self.lastPriceList[i]+10, pos[i], False)
                self.writeCtaLog(u'%s平空,数量：%s,价格：%s' %(i, pos[i],self.lastPriceList[i]+10))
            else:
                pass
        
        
    #----------------------------------------------------------------------
    def onTrade(self, trade):
        """成交回报"""
        symbol = trade.symbol
        self.writeCtaLog(u'%s成交回报, 单号：%s, 方向：%s，价格：%s，offset：%s, 数量：%s' %(symbol, trade.vtOrderID, trade.direction, trade.price, trade.offset, trade.volume))
        
        if self.turtlePositionList[trade.symbol] == None:
            self.writeCtaLog(u'%s持仓对象错误' %symbol)
            return
        
        t = self.turtlePositionList[trade.symbol]

        if self.pos[trade.symbol] != t.totalPosition + trade.volume:
            self.writeCtaLog(u'%s持仓数量错误，pos1：%s，pos2：%s' %(symbol, self.pos[trade.symbol], t.totalPosition))
        
        #删除正在执行的报单列表对应表项
        if trade.direction == DIRECTION_LONG and trade.vtOrderID in self.workingBuyList.values():
            if self.workingBuyList[symbol] == trade.vtOrderID:
                self.writeCtaLog(u'%s报单已成交，报单号：%s' %(symbol, trade.vtOrderID))                
                del self.workingBuyList[symbol]
            else:
                self.writeCtaLog(u'%s订单错误，ID1：%s，ID2：%s' %(symbol, trade.vtOrderID, self.workingBuyList[symbol]))
        elif trade.direction == DIRECTION_SHORT and trade.vtOrderID in self.workingShortList.values():
            if self.workingShortList[symbol] == trade.vtOrderID:
                self.writeCtaLog(u'%s空单已成交，报单号：%s' %(symbol, trade.vtOrderID))                
                del self.workingShortList[symbol]
            else:
                self.writeCtaLog(u'%s订单错误，ID1：%s，ID2：%s' %(symbol, trade.vtOrderID, self.workingShortList[symbol]))
        else:
            self.writeCtaLog(u'%s订单已成交，报单号：%s，方向错误：%s' %(symbol, trade.vtOrderID, trade.direction))
    
        if t.totalPosition == 0:
            #开仓
            t.updateTradeData(trade)
            #pos在engine中已经更新，此处无需更新，这里感觉需要修改下，现在结构比较乱            
            #self.pos[trade.symbol] += trade.volume            
        elif t.direction == trade.direction:
            #加仓成交
            t.updateTradeData(trade)
            #pos在engine中已经更新，此处无需更新
            #self.pos[trade.symbol] += trade.volume
        else:
            self.writeCtaLog(u'%s止损成交' %symbol)
            #stop order trade return
            if self.pos[symbol] != 0:
                #止损单未全部成交
                self.writeCtaLog(u'%s止损成交数量错误' %symbol)
            else: 
                self.stopPriceList[symbol] = EMPTY_FLOAT
                t.updateStopData(trade)

            #self.pos[trade.symbol] -= trade.volume

        #set price
        self.setPriceList(symbol)
        self.putEvent()
        
    #----------------------------------------------------------------------
    def setPriceList(self, symbol):
        """更新对应的price list, send stop order, MUST be called after update turtle"""
        
        #更新对应的price list
        if self.pos[symbol] == 0:
            #没有持仓，开仓价格为20日新高
            self.buyPriceList[symbol] = self.twentyDayHigh[symbol]
            self.shortPriceList[symbol] = self.twentyDayLow[symbol]
        else:
            if self.workingStopList.has_key(symbol) and self.workingStopList[symbol] != "":
                self.cancelOrder(self.workingStopList[symbol])
            else:
                #没有运行中的止损单
                pass

            #有持仓，使用海龟计算出来的开仓价格
            if self.turtlePositionList[symbol] == None:
                self.writeCtaLog(u'%s 持仓对象错误' %symbol)
            else:
                t = self.turtlePositionList[symbol]

                if t.direction == DIRECTION_LONG:
                    self.buyPriceList[symbol] = t.currentOpenPrice
                    self.shortPriceList[symbol] = -1
                    self.stopPriceList[symbol] = max(t.currentStopPrice, self.tenDayLow[symbol])
                elif t.direction == DIRECTION_SHORT:
                    self.buyPriceList[symbol] = -1
                    self.shortPriceList[symbol] = t.currentOpenPrice
                    self.stopPriceList[symbol] = min(t.currentStopPrice, self.tenDayHigh[symbol])
                else:
                    self.writeCtaLog(u'%s方向错误' %symbol)
                
                if t.currentState == TURTLE_OPEN_FOUR:
                    #no open price needed
                    self.buyPriceList[symbol] = -1
                    self.shortPriceList[symbol] = -1

                #send stop order
                if self.stopPriceList[symbol] > 0:
                    if t.direction == DIRECTION_LONG:
                        orderID = self.sell(symbol, self.stopPriceList[symbol], t.totalPosition, True)
                        self.writeCtaLog(u'%s更新多单止损单：价格:%d, 手数：%d， 合约号: %s' %(symbol, self.stopPriceList[symbol], t.totalPosition, orderID)) 
                    elif t.direction == DIRECTION_SHORT:
                        orderID = self.cover(symbol, self.stopPriceList[symbol], -t.totalPosition, True)
                        self.writeCtaLog(u'%s更新空单止损单：价格:%d, 手数：%d， 合约号: %s' %(symbol, self.stopPriceList[symbol], t.totalPosition, orderID))                     

                    if orderID != "":
                        self.workingStopList[symbol] = orderID
                else:
                    self.writeCtaLog(u'%s止损价格错误' %symbol)                    


    #----------------------------------------------------------------------
    def loadCurrentPosition(self, order):
        """return current turtle position"""
        pass

    #----------------------------------------------------------------------
    def saveTurtlePosition(self, order):
        """save current turtle position"""
        pass

    #----------------------------------------------------------------------
    def calculateOpenPosition(self, symbol, price, atr):
        """return current turtle position"""
        #从main engine获取合约的单位和最小tick价格
        # TODO: 保证金比例现在都按照10%来计算
        # 计算方式：N / (ATR * 合约单位 * 合约价格)
        # N为总资金的 0.35% ， 先假定1000000
        if self.balance != 0:
            N = self.balance * 0.0035             
        else:
            N = 1000000 * 0.0035 

        contract = self.ctaEngine.mainEngine.getContract(symbol)
        
        #返回整数部分
        i = int(N // (atr * contract.size))
        if  i <= 0:
            self.writeCtaLog(u'总资金不足，无法开仓：%s' %symbol)
            i = 1
        return i  

    #----------------------------------------------------------------------
    def saveTurtlePosition(self):
        """保存所有合约对象到硬盘"""

        f = shelve.open(self.turtleFileName)
        f['data'] = self.turtlePositionList
        print "save:", len(self.contractDict)
        f.close()
    
    #----------------------------------------------------------------------
    def loadTurtlePosition(self):
        """从硬盘读取合约对象"""
        f = shelve.open(self.turtleFileName)
        if 'data' in f:
            d = f['data']
            #print "load:", len(d), len(self.contractDict)
            
            for key, value in d.items():
                self.contractDict[key] = value
            
            #tmp = sorted(self.contractDict.iteritems())
            #for key in tmp:
                #print "[\""+key[0]+"\", "+ "\"CTP\"],"
            
        f.close()

    #----------------------------------------------------------------------        
    def putEvent(self):
        """发送dump"""

        if self.debugInit:
            c = self.dumpTurtle()            
            for k in c:
                event = Event(type_=EVENT_CTA_MONITOR)
                c[k]['time'] = time.strftime('%X', time.localtime())    # 日志生成时间
                event.dict_['data'] = c[k]
                self.ctaEngine.eventEngine.put(event)
        
        super(TurtleStrategy, self).putEvent()

    #----------------------------------------------------------------------
    def dumpTurtle(self):
        """dump turtle"""

        paramDict = {}
        for key in self.paramList:  
            paramDict[key] = self.__getattribute__(key)

        contDict = {}
        for k in paramDict['vtSymbolList']:
            contDict[k] = {}
            contDict[k]['symbol'] = k

            #load from turtlePosition Object
            if self.turtlePositionList[k] != None:
                contDict[k]['turtleState'] = self.turtlePositionList[k].currentState
                contDict[k]['turtlePos'] = self.turtlePositionList[k].totalPosition
                contDict[k]['tDirection'] = self.turtlePositionList[k].direction
                contDict[k]['tFirstPrice'] = self.turtlePositionList[k].firstOpenPrice
                contDict[k]['tFirstPos'] = self.turtlePositionList[k].firstOpenPosition
                contDict[k]['tFirstDate'] = self.turtlePositionList[k].firstOpenDatetime
                contDict[k]['tSecondPrice'] = self.turtlePositionList[k].secondOpenPrice
                contDict[k]['tSecondPos'] = self.turtlePositionList[k].secondOpenPosition
                contDict[k]['tSecondDate'] = self.turtlePositionList[k].secondOpenDatetime
                contDict[k]['tThirdPrice'] = self.turtlePositionList[k].thirdOpenPrice
                contDict[k]['tThridPos'] = self.turtlePositionList[k].thirdOpenPosition
                contDict[k]['tThirdDate'] = self.turtlePositionList[k].thirdOpenDatetime
                contDict[k]['tFourthPrice'] = self.turtlePositionList[k].fourthOpenPrice
                contDict[k]['tFourthPos'] = self.turtlePositionList[k].fourthOpenPosition
                contDict[k]['tFourthDate'] = self.turtlePositionList[k].fourthOpenDatetime
                contDict[k]['tOpenPrice'] = self.turtlePositionList[k].currentOpenPrice
                contDict[k]['tStopPrice'] = self.turtlePositionList[k].currentStopPrice
            else:
                contDict[k]['turtleState'] = ""
                contDict[k]['turtleState'] = ""
                contDict[k]['turtlePos'] = ""
                contDict[k]['tDirection'] = ""
                contDict[k]['tFirstPrice'] = ""
                contDict[k]['tFirstPos'] = ""
                contDict[k]['tFirstDate'] = ""
                contDict[k]['tSecondPrice'] = ""
                contDict[k]['tSecondPos'] = ""
                contDict[k]['tSecondDate'] = ""
                contDict[k]['tThirdPrice'] = ""
                contDict[k]['tThridPos'] = ""
                contDict[k]['tThirdDate'] = ""
                contDict[k]['tFourthPrice'] = ""
                contDict[k]['tFourthPos'] = ""
                contDict[k]['tFourthDate'] = ""
                contDict[k]['tOpenPrice'] = ""
                contDict[k]['tStopPrice'] = ""
                
            #load from global param dict
            for key1 in paramDict.keys():
                if isinstance(paramDict[key1], dict):
                    if paramDict[key1].has_key(k):
                        contDict[k][key1] = paramDict[key1][k]
                        #print key1 + ":" + str(contDict[k][key1])
        
        #print "@@@@@@@@@@@@@@@@@@@@@@@@@@@@finish dump"
        return contDict

class turtlePosition(object):
    """turtle position"""

    
    #----------------------------------------------------------------------
    def __init__(self, strategy):
        """Constructor"""
        self.strategy = strategy           #only use for write log
        
        self.vtSymbol = EMPTY_STRING        # vt系统代码
        self.symbol = EMPTY_STRING          # 代码
        self.exchange = EMPTY_STRING        # 交易所
    
        self.currentState = TURTLE_READY
        
        self.firstOpenPrice = EMPTY_FLOAT
        self.firstOpenPosition = EMPTY_INT
        self.firstOpenDatetime = None       # python的datetime时间对象
        self.firstOpenAtr = EMPTY_FLOAT     # atr for first open position
        self.secondOpenPrice = EMPTY_FLOAT
        self.secondOpenPosition = EMPTY_INT
        self.secondOpenDatetime = None       # python的datetime时间对象
        self.secondOpenAtr = EMPTY_FLOAT     # atr for first open position
        self.thirdOpenPrice = EMPTY_FLOAT
        self.thirdOpenPosition = EMPTY_INT
        self.thirdOpenDatetime = None       # python的datetime时间对象
        self.thirdOpenAtr = EMPTY_FLOAT     # atr for first open position        
        self.fourthOpenPrice = EMPTY_FLOAT
        self.fourthOpenPosition = EMPTY_INT
        self.fourthOpenDatetime = None       # python的datetime时间对象
        self.fourthOpenAtr = EMPTY_FLOAT     # atr for first open position
        
        self.currentOpenPrice = EMPTY_FLOAT  #open price for this trade
        self.currentStopPrice = EMPTY_FLOAT  #stop price for this trade
        self.direction = EMPTY_STRING        #direction
        self.currentOpenAtr = EMPTY_FLOAT    #atr
        
        self.openDatetime = None                # python的datetime时间对象
        
        self.totalPosition = EMPTY_INT             # holding position

    
    def updateTradeData(self, trade):
        """buy one position"""
        symbol = trade.symbol
        if trade.symbol != self.symbol or trade.vtSymbol != self.vtSymbol:
            self.writeCtaLog(u'%s合约错误，持仓状态：%s' %(symbol, self.currentState))
            return

        if self.currentState != TURTLE_READY:
            if trade.direction != self.direction:
                self.writeCtaLog(u'%s交易方向错误，持仓状态：%s' %(symbol, self.currentState))

        if self.currentState == TURTLE_READY:
            #开仓
            self.direction = trade.direction

            self.firstOpenPrice = trade.price
            self.firstOpenDatetime = trade.tradeTime
            self.firstOpenAtr = self.currentOpenAtr
            atr = self.currentOpenAtr
            
            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = self.firstOpenPrice + atr/2
                self.currentStopPrice = self.firstOpenPrice - 2*atr
                self.totalPosition += trade.volume                
                self.firstOpenPosition = trade.volume                
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = self.firstOpenPrice - atr/2
                self.currentStopPrice = self.firstOpenPrice + 2*atr
                self.totalPosition -= trade.volume                
                self.firstOpenPosition = -trade.volume                
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))
                pass

            self.currentState = TURTLE_OPEN_ONE
            
        elif self.currentState == TURTLE_OPEN_ONE:
            self.secondOpenPrice = trade.price
            self.secondOpenDatetime = trade.tradeTime
            self.secondOpenAtr = self.currentOpenAtr
            
            atr = self.currentOpenAtr
            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = self.secondOpenPrice + atr/2
                self.currentStopPrice = self.secondOpenPrice - 2*atr
                self.totalPosition += trade.volume                
                self.secondOpenPosition = trade.volume
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = self.secondOpenPrice - atr/2
                self.currentStopPrice = self.secondOpenPrice + 2*atr
                self.totalPosition -= trade.volume                
                self.secondOpenPosition = -trade.volume                
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))
                pass

            self.currentState = TURTLE_OPEN_TWO

        elif self.currentState == TURTLE_OPEN_TWO:
            self.thirdOpenPrice = trade.price
            self.thirdOpenDatetime = trade.tradeTime
            self.thirdOpenAtr = self.currentOpenAtr
            atr = self.currentOpenAtr            
            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = self.thirdOpenPrice + atr/2
                self.currentStopPrice = self.thirdOpenPrice - 2*atr
                self.totalPosition += trade.volume                
                self.thirdOpenPosition = trade.volume                
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = self.thirdOpenPrice - atr/2
                self.currentStopPrice = self.thirdOpenPrice + 2*atr
                self.totalPosition -= trade.volume                
                self.thirdOpenPosition = -trade.volume
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))

            self.currentState = TURTLE_OPEN_THREE
            
        elif self.currentState == TURTLE_OPEN_THREE:
            self.fourthOpenPrice = trade.price
            self.fourthOpenDatetime = trade.tradeTime
            self.fourthOpenAtr = self.currentOpenAtr
            atr = self.currentOpenAtr            

            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = -1
                self.currentStopPrice = self.fourthOpenPrice - 2*atr
                self.totalPosition += trade.volume                
                self.fourthOpenPosition = trade.volume
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = -1
                self.currentStopPrice = self.fourthOpenPrice + 2*atr
                self.totalPosition -= trade.volume    
                self.fourthOpenPosition = -trade.volume                
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))
    
            self.currentState = TURTLE_OPEN_FOUR

        elif self.currentState == TURTLE_OPEN_FOUR:
            #should not get here
            self.writeCtaLog(u'%s交易状态错误，持仓状态：%s' %(symbol, self.currentState))
        else:
            self.writeCtaLog(u'%s交易状态错误，持仓状态：%s' %(symbol, self.currentState))

    
    def updateAtrData(self, atr):
        """update conresponding data use new atr"""
        
        self.currentOpenAtr = atr
        symbol = self.symbol
        
        if self.currentState == TURTLE_READY:
            #do nothing
            pass
        elif self.currentState == TURTLE_OPEN_ONE:
            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = self.firstOpenPrice + atr/2
                self.currentStopPrice = self.firstOpenPrice - 2*atr
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = self.firstOpenPrice - atr/2
                self.currentStopPrice = self.firstOpenPrice + 2*atr
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))
        elif self.currentState == TURTLE_OPEN_TWO:
            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = self.secondOpenPrice + atr/2
                self.currentStopPrice = self.secondOpenPrice - 2*atr
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = self.secondOpenPrice - atr/2
                self.currentStopPrice = self.secondOpenPrice + 2*atr
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))
        elif self.currentState == TURTLE_OPEN_THREE:
            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = self.thirdOpenPrice + atr/2
                self.currentStopPrice = self.thirdOpenPrice - 2*atr
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = self.thirdOpenPrice - atr/2
                self.currentStopPrice = self.thirdOpenPrice + 2*atr
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))
        elif self.currentState == TURTLE_OPEN_FOUR:
            if self.direction == DIRECTION_LONG:
                self.currentOpenPrice = self.fourthOpenPrice + atr/2
                self.currentStopPrice = self.fourthOpenPrice - 2*atr
            elif self.direction == DIRECTION_SHORT:
                self.currentOpenPrice = self.fourthOpenPrice - atr/2
                self.currentStopPrice = self.fourthOpenPrice + 2*atr
            else:
                self.writeCtaLog(u'%s方向错误，持仓状态：%s' %(symbol, self.currentState))
        else:
            self.writeCtaLog(u'%s状态错误，持仓状态：%s' %(symbol, self.currentState))

    
    def updateStopData(self, trade):
        """update stop order"""
        #reset all members 
        self.currentState = TURTLE_READY
        
        self.firstOpenPrice = EMPTY_FLOAT
        self.firstOpenPosition = EMPTY_INT
        self.firstOpenDatetime = None       # python的datetime时间对象
        self.firstOpenAtr = EMPTY_FLOAT     # atr for first open position
        self.secondOpenPrice = EMPTY_FLOAT
        self.secondOpenPosition = EMPTY_INT
        self.secondOpenDatetime = None       # python的datetime时间对象
        self.secondOpenAtr = EMPTY_FLOAT     # atr for first open position
        self.thirdOpenPrice = EMPTY_FLOAT
        self.thirdOpenPosition = EMPTY_INT
        self.thirdOpenDatetime = None       # python的datetime时间对象
        self.thirdOpenAtr = EMPTY_FLOAT     # atr for first open position        
        self.fourthOpenPrice = EMPTY_FLOAT
        self.fourthOpenPosition = EMPTY_INT
        self.fourthOpenDatetime = None       # python的datetime时间对象
        self.fourthOpenAtr = EMPTY_FLOAT     # atr for first open position
        
        self.currentOpenPrice = EMPTY_FLOAT  #open price for this trade
        self.currentStopPrice = EMPTY_FLOAT  #stop price for this trade
        self.direction = EMPTY_STRING        #direction
        self.currentOpenAtr = EMPTY_FLOAT    #atr
        
        self.openDatetime = None                # python的datetime时间对象
        
        self.totalPosition = EMPTY_INT             # holding position
    
    #----------------------------------------------------------------------
    def writeCtaLog(self, content):
        """记录CTA日志"""
        content = 'turtlePosition:' + content
        self.strategy.writeCtaLog(content)
        
if __name__ == '__main__':
    #----------------------------------------------------------------------
    def sa(a):
        """保存所有合约对象到硬盘"""

        f = shelve.open("turtleFileName")
        f['data'] = a
        print "save:", len(a)
        f.close()    

    #n = turtlePosition()
    #s = {"tmp":n}
    #sa(s)
    
    
"""
    # 提供直接双击回测的功能
    # 导入PyQt4的包是为了保证matplotlib使用PyQt4而不是PySide，防止初始化出错
    from ctaBacktesting import *
    from PyQt4 import QtCore, QtGui
    
    # 创建回测引擎
    engine = BacktestingEngine()
    
    # 设置引擎的回测模式为K线
    engine.setBacktestingMode(engine.BAR_MODE)

    # 设置回测用的数据起始日期
    engine.setStartDate('20120101')
    
    # 设置产品相关参数
    engine.setSlippage(0.2)     # 股指1跳
    engine.setRate(0.3/10000)   # 万0.3
    engine.setSize(300)         # 股指合约大小        
    
    # 设置使用的历史数据库
    engine.setDatabase(MINUTE_DB_NAME, 'IF0000')
    
    # 在引擎中创建策略对象
    d = {'atrLength': 11}
    engine.initStrategy(AtrRsiStrategy, d)
    
    # 开始跑回测
    engine.runBacktesting()
    
    # 显示回测结果
    engine.showBacktestingResult()
    
    ## 跑优化
    #setting = OptimizationSetting()                 # 新建一个优化任务设置对象
    #setting.setOptimizeTarget('capital')            # 设置优化排序的目标是策略净盈利
    #setting.addParameter('atrLength', 11, 12, 1)    # 增加第一个优化参数atrLength，起始11，结束12，步进1
    #setting.addParameter('atrMa', 20, 30, 5)        # 增加第二个优化参数atrMa，起始20，结束30，步进1
    #engine.runOptimization(AtrRsiStrategy, setting) # 运行优化函数，自动输出结果
"""        
    