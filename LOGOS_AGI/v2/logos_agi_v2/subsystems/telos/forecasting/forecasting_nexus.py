import traceback
from pmdarima import auto_arima
from arch import arch_model

class ForecastingNexus:
    def run_pipeline(self, series, horizon=5):
        report = []
        try:
            arima_fit = auto_arima(series, seasonal=False, suppress_warnings=True, error_action='ignore')
            arima_fc = arima_fit.predict(n_periods=horizon)
            report.append({'stage': 'arima', 'output': list(arima_fc)})
        except Exception as e:
            report.append({'stage': 'arima', 'error': traceback.format_exc()})
        try:
            returns = [series[i] - series[i-1] for i in range(1, len(series))]
            if len(returns) < 5:
                raise ValueError("Not enough data for GARCH model.")
            garch_fit = arch_model(returns, vol='Garch', p=1, q=1).fit(disp='off')
            garch_fc = garch_fit.forecast(horizon=horizon)
            report.append({'stage': 'garch', 'output': garch_fc.variance.iloc[-1].tolist()})
        except Exception as e:
             report.append({'stage': 'garch', 'error': str(e)})
        return report
